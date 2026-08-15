#!/usr/bin/env python3
"""
huurbot - monitor Dutch rental sites for new listings and email you when
something new shows up.

Usage:
    python huurbot.py --check-config    # validate config, show parsed filters
    python huurbot.py --test-email      # send yourself a test email
    python huurbot.py --once            # run a single check and exit
    python huurbot.py --seed            # mark everything currently online as
                                        # "seen" without emailing (do this first)
    python huurbot.py                   # run forever
    python huurbot.py --dump            # save raw HTML to debug/ for fixing selectors
"""

from __future__ import annotations

import argparse
import hashlib
import html
import json
import logging
import os
import random
import re
import smtplib
import sqlite3
import sys
import time
from dataclasses import dataclass, field, asdict
from datetime import datetime, timedelta, timezone
from email.message import EmailMessage
from pathlib import Path
from typing import Iterable, Optional
from urllib.parse import quote, urljoin, urlparse

import yaml
from bs4 import BeautifulSoup

# curl_cffi impersonates a real browser's TLS fingerprint, which gets past a lot
# of the basic bot filtering that plain `requests` trips. Optional but recommended.
try:
    from curl_cffi import requests as http  # type: ignore
    HAVE_CURL_CFFI = True
except ImportError:  # pragma: no cover
    import requests as http  # type: ignore
    HAVE_CURL_CFFI = False

BASE_DIR = Path(__file__).resolve().parent
DB_PATH = BASE_DIR / "seen.sqlite3"
DEBUG_DIR = BASE_DIR / "debug"

log = logging.getLogger("huurbot")


# --------------------------------------------------------------------------
# Data model
# --------------------------------------------------------------------------

@dataclass
class Listing:
    site: str
    url: str
    title: str = ""
    address: str = ""
    price: Optional[int] = None          # euros per month
    size_m2: Optional[int] = None
    rooms: Optional[int] = None
    bedrooms: Optional[int] = None
    agent: str = ""
    image: str = ""
    raw_text: str = ""
    # Optional extra identity. Most sites give each listing its own URL, so the
    # URL alone is enough. Some pages instead show a row per building whose URL
    # never changes while the number of available homes does -- those set a
    # fingerprint so a change counts as something new.
    fingerprint: str = ""

    @property
    def key(self) -> str:
        """Stable identity for a listing. URL path, ignoring query params."""
        p = urlparse(self.url)
        return hashlib.sha1(f"{p.netloc}{p.path}{self.fingerprint}".encode()).hexdigest()

    def summary(self) -> str:
        bits = []
        if self.price:
            bits.append(f"EUR {self.price}/mo")
        if self.size_m2:
            bits.append(f"{self.size_m2} m2")
        if self.rooms:
            bits.append(f"{self.rooms} rooms")
        return " | ".join(bits)


# --------------------------------------------------------------------------
# Parsing helpers
# --------------------------------------------------------------------------

def _clean(s: str) -> str:
    return re.sub(r"\s+", " ", (s or "")).strip()


def parse_price(text: str) -> Optional[int]:
    """'€ 1.750 per maand' -> 1750.  '€1,750' -> 1750."""
    if not text:
        return None
    m = re.search(r"€\s*([\d][\d.,]*)", text)
    if not m:
        m = re.search(r"\b(\d[\d.,]{2,})\b", text)
        if not m:
            return None
    num = m.group(1)
    # Strip thousand separators (both . and , are used depending on locale)
    num = re.sub(r"[.,](?=\d{3}\b)", "", num)
    num = num.replace(",", ".")
    try:
        val = float(num)
    except ValueError:
        return None
    if val <= 0 or val > 100_000:
        return None
    return int(val)


def parse_int_before(text: str, *keywords: str) -> Optional[int]:
    """Find '75 m2' / '3 kamers' / '2 bedrooms' style numbers."""
    for kw in keywords:
        m = re.search(rf"(\d+)\s*{kw}", text, flags=re.I)
        if m:
            return int(m.group(1))
    return None


def parse_size(text: str) -> Optional[int]:
    return parse_int_before(text, r"m²", r"m2", r"\bsqm\b")


# --------------------------------------------------------------------------
# Site adapters
#
# Each adapter takes the page HTML and returns Listings. If a site changes its
# markup, only the adapter needs fixing -- run with --dump to grab the raw HTML
# and inspect it.
# --------------------------------------------------------------------------

def parse_pararius_family(soupurl: str, soup: BeautifulSoup, site: str) -> list[Listing]:
    """
    Pararius.nl / Pararius.com / Huurwoningen.nl share a codebase, so one parser
    covers all three. Listings live in <section class="listing-search-item">.
    """
    out: list[Listing] = []
    # Try the innermost container first -- selecting both <section> and its
    # parent <li> would yield every listing twice.
    cards = soup.select("section.listing-search-item")
    if not cards:
        cards = soup.select("li.search-list__item--listing, div[class*='listing-search-item']")
    for card in cards:
        # Pararius listing URLs are language-specific and NOT what you'd guess:
        #   .com  /apartment-for-rent/amsterdam/<hash>/<street>
        #         /studio-for-rent/... /house-for-rent/... /room-for-rent/...
        #   .nl   /appartement-te-huur/... /huurwoning/...
        # Huurwoningen.nl uses /huurwoning/. Match all of them.
        #
        # Try the TITLE link first. A comma-separated selector returns whichever
        # matches first in document order, which is the thumbnail -- and that
        # has no text, so the title would be lost.
        link = (card.select_one('a.listing-search-item__link--title')
                or card.select_one('h2 a, h3 a')
                or card.select_one('a[href*="-for-rent/"], a[href*="-te-huur/"], '
                                   'a[href*="/huurwoning"]'))
        if not link or not link.get("href"):
            continue
        url = urljoin(soupurl, link["href"])
        text = _clean(card.get_text(" "))

        price_el = card.select_one('[class*="price"]')
        sub_el = card.select_one('[class*="sub-title"], [class*="location"]')
        # The agent is reliably the link pointing at an agent profile; the
        # wrapper's class name varies between their sites.
        agent_el = (card.select_one('a[href*="/real-estate-agents/"], a[href*="/makelaar"]')
                    or card.select_one('[class*="info-container"] a, [class*="agent"]'))
        img_el = card.select_one("img")

        listing = Listing(
            site=site,
            url=url,
            title=_clean(link.get_text()) or _clean(link.get("title", "")),
            address=_clean(sub_el.get_text()) if sub_el else "",
            price=parse_price(_clean(price_el.get_text()) if price_el else text),
            size_m2=parse_size(text),
            rooms=parse_int_before(text, "kamers", "kamer", "rooms", "room"),
            bedrooms=parse_int_before(text, "slaapkamers", "slaapkamer", "bedrooms", "bedroom"),
            agent=_clean(agent_el.get_text()) if agent_el else "",
            image=(img_el.get("src") or img_el.get("data-src") or "") if img_el else "",
            raw_text=text[:500],
        )
        out.append(listing)
    return out


def parse_ikwilhuren(soupurl: str, soup: BeautifulSoup, site: str) -> list[Listing]:
    """
    ikwilhuren.nu (MVGM's own rental portal). Fully server-rendered, no bot
    protection, listing URLs are /object/<city>-<postcode>-<nr>-<street>-<hash>/.

    Card text looks like:
        Appartement Elzenhagensingel 389
        1022LA Amsterdam - 4Km. Direct beschikbaar ... Nieuw
        € 2.280,- /mnd 90 m2 2 slaapkamers

    Anchored on the URL pattern rather than CSS classes, so a restyle won't
    break it.
    """
    out: list[Listing] = []
    for a in soup.select('a[href*="/object/"]'):
        url = urljoin(soupurl, a["href"])

        # Walk up until we hit the block that also contains the price
        card = a
        for _ in range(6):
            if card.parent is None:
                break
            card = card.parent
            if "€" in card.get_text() and len(card.get_text(strip=True)) > 40:
                break
        text = _clean(card.get_text(" "))

        # The thumbnail and the title link to the same listing. The thumbnail
        # anchor has no text, so emit it as an image-only record and let the
        # dedupe step merge it into the titled one.
        title = _clean(a.get_text())
        if not title:
            img = a.select_one("img")
            if img and (img.get("src") or img.get("data-src")):
                out.append(Listing(site=site, url=url,
                                   image=img.get("src") or img.get("data-src")))
            continue

        # "1022LA Amsterdam - 4Km." -> postcode + city
        addr = ""
        m = re.search(r"\b(\d{4}\s?[A-Z]{2})\s+([A-Za-z\u00c0-\u017f\s'-]+?)(?:\s*-\s*\d+\s*Km|\s{2,}|$)", text)
        if m:
            addr = f"{m.group(1)} {_clean(m.group(2))}"

        avail = ""
        ma = re.search(r"(Direct beschikbaar|Beschikbaar vanaf\s+[\d-]+)", text, re.I)
        if ma:
            avail = ma.group(1)

        img_el = card.select_one("img")
        out.append(Listing(
            site=site,
            url=url,
            title=title,
            address=addr or avail,
            price=parse_price(text),
            size_m2=parse_size(text),
            bedrooms=parse_int_before(text, "slaapkamers", "slaapkamer", "bedrooms", "bedroom"),
            agent="MVGM" + (f" \u00b7 {avail}" if avail else ""),
            image=(img_el.get("src") or img_el.get("data-src") or "") if img_el else "",
            raw_text=text[:500],
        ))
    return out


def parse_vesteda(soupurl: str, soup: BeautifulSoup, site: str) -> list[Listing]:
    """
    vesteda.com -- a large Dutch landlord, so no agency fees.

    Their per-home search results are rendered in JavaScript, so plain HTTP
    can't see them. The per-building list on a city page IS in the HTML though,
    and carries how many homes are free and the price range:

        De Enter    Amsterdam    4 woningen    EUR 1545 - EUR 2125

    That's what we watch. When the count or the price range changes, something
    became available -- so the fingerprint includes both, making a change look
    like a new listing. You then click through to see the individual homes.
    """
    out: list[Listing] = []
    rx = re.compile(r"/huurwoningen-[a-z-]+/[a-z0-9-]+")
    for a in soup.find_all("a", href=True):
        if not rx.search(a["href"]):
            continue
        url = urljoin(soupurl, a["href"])
        title = _clean(a.get_text())
        if not title or len(title) > 90:
            continue

        # Climb to the card that carries the counts and prices
        card = a
        for _ in range(6):
            if card.parent is None:
                break
            card = card.parent
            if "woning" in card.get_text() and "€" in card.get_text():
                break
        text = _clean(card.get_text(" "))

        count = None
        mc = re.search(r"(\d+)\s+woning", text, re.I)
        if mc:
            count = int(mc.group(1))

        prices = []
        for pm in re.finditer(r"€\s*([\d][\d.,]*)", text):
            v = parse_price("€" + pm.group(1))
            if v:
                prices.append(v)
        lo = min(prices) if prices else None
        hi = max(prices) if prices else None

        if count is None and lo is None:
            continue  # not a project card, just a stray link

        span = f"€{lo}" + (f"–€{hi}" if hi and hi != lo else "") if lo else ""
        city = ""
        mcity = re.search(r"/huurwoningen-([a-z-]+)/", a["href"])
        if mcity:
            city = mcity.group(1).replace("-", " ").title()

        out.append(Listing(
            site=site,
            url=url,
            title=title,
            address=f"{city}" + (f" · {count} woning{'en' if count != 1 else ''} beschikbaar"
                                 if count else ""),
            price=lo,                       # cheapest, so max_price still filters sensibly
            agent="Vesteda",
            raw_text=f"{text[:300]} {city}",
            fingerprint=f"{count}|{lo}|{hi}",
        ))
    return out


def parse_vbt(soupurl: str, soup: BeautifulSoup, site: str) -> list[Listing]:
    """
    vbtverhuurmakelaars.nl -- fully server-rendered, richest data of the lot.

    Card text runs together like:
        Beschikbaar AmsterdamHiraistraat 3 C44 EUR 1.303,-
        Soort object Appartement | Woonoppervlakte 61 m2 | Kamers 2 Kamers
        Servicekosten EUR 125,- per maand | Aantal reacties 94

    Two things worth knowing:
      - The rent is the FIRST euro figure; a later one is service charges.
      - "Aantal reacties" is how many people have already applied. Surfaced in
        the alert, because 2 applicants and 94 applicants are very different
        propositions.
    """
    out: list[Listing] = []
    for a in soup.select('a[href*="/woning/"]'):
        url = urljoin(soupurl, a["href"])
        slug = urlparse(url).path.rstrip("/").rsplit("/", 1)[-1]
        text = _clean(a.get_text(" "))
        if not text:
            card = a.parent
            text = _clean(card.get_text(" ")) if card else ""

        # City is the first slug segment; the rest is the street
        city, street = "", slug.replace("-", " ").title()
        m = re.match(r"(s-gravenhage|[a-z]+)-(.+)", slug)
        if m:
            city = m.group(1).replace("-", " ").title()
            street = m.group(2).replace("-", " ").title()

        reacties = None
        mr = re.search(r"Aantal reacties\s*\|?\s*(\d+)", text, re.I)
        if mr:
            reacties = int(mr.group(1))

        avail = ""
        ma = re.search(r"Beschikbaar\s*\|?\s*(\d{1,2}\s+\w+\s+\d{4})", text, re.I)
        if ma:
            avail = ma.group(1)

        listing = Listing(
            site=site,
            url=url,
            title=street,
            address=city + (f" · beschikbaar {avail}" if avail else ""),
            price=parse_price(text),        # first euro figure = the rent
            size_m2=parse_size(text),
            rooms=parse_int_before(text, "Kamers", "kamers"),
            agent="vb&t" + (f" · {reacties} reacties" if reacties is not None else ""),
            raw_text=f"{text[:400]} {city}",
        )
        if listing.price or listing.size_m2:
            out.append(listing)
    return out


def parse_jsonld(soupurl: str, soup: BeautifulSoup, site: str) -> list[Listing]:
    """
    Generic fallback: many property sites embed schema.org JSON-LD, which is far
    more stable than CSS classes.
    """
    out: list[Listing] = []
    for tag in soup.find_all("script", type="application/ld+json"):
        try:
            data = json.loads(tag.string or "")
        except (json.JSONDecodeError, TypeError):
            continue
        stack = [data]
        while stack:
            node = stack.pop()
            if isinstance(node, list):
                stack.extend(node)
                continue
            if not isinstance(node, dict):
                continue
            stack.extend(v for v in node.values() if isinstance(v, (dict, list)))

            ntype = str(node.get("@type", ""))
            if ntype not in {"Residence", "Apartment", "House", "SingleFamilyResidence",
                             "Product", "Offer", "RealEstateListing"}:
                continue
            url = node.get("url") or node.get("@id")
            if not url or not isinstance(url, str):
                continue

            offers = node.get("offers") or {}
            if isinstance(offers, list):
                offers = offers[0] if offers else {}
            price = offers.get("price") if isinstance(offers, dict) else None

            addr = node.get("address")
            if isinstance(addr, dict):
                addr = " ".join(
                    str(addr.get(k, "")) for k in
                    ("streetAddress", "postalCode", "addressLocality")
                )
            out.append(Listing(
                site=site,
                url=urljoin(soupurl, url),
                title=_clean(str(node.get("name", ""))),
                address=_clean(str(addr or "")),
                price=parse_price(str(price)) if price else None,
                image=str(node.get("image") or "") if isinstance(node.get("image"), str) else "",
            ))
    return out


def parse_generic_links(soupurl: str, soup: BeautifulSoup, site: str,
                        pattern: str) -> list[Listing]:
    """
    Last-resort parser: grab every anchor whose href matches a listing-URL
    pattern and pull text from its surrounding block. Ugly but survives most
    redesigns, so you still get alerts while you fix the real adapter.
    """
    out: list[Listing] = []
    seen: set[str] = set()
    rx = re.compile(pattern)
    for a in soup.find_all("a", href=True):
        if not rx.search(a["href"]):
            continue
        url = urljoin(soupurl, a["href"])
        pkey = urlparse(url).path
        if pkey in seen:
            continue
        seen.add(pkey)

        block = a
        for _ in range(4):
            if block.parent is None:
                break
            block = block.parent
            if len(block.get_text(strip=True)) > 60:
                break
        text = _clean(block.get_text(" "))[:500]
        out.append(Listing(
            site=site,
            url=url,
            title=_clean(a.get_text()) or pkey.rsplit("/", 1)[-1].replace("-", " "),
            price=parse_price(text),
            size_m2=parse_size(text),
            rooms=parse_int_before(text, "kamers", "rooms"),
            raw_text=text,
        ))
    return out


# name -> (parser, listing-url-regex for the generic fallback)
ADAPTERS = {
    "pararius":     (parse_pararius_family, r"(-for-rent|-te-huur)/|/huurwoning"),
    "huurwoningen": (parse_pararius_family, r"(-for-rent|-te-huur)/|/huurwoning"),
    "ikwilhuren":   (parse_ikwilhuren,      r"/object/"),
    "vesteda":      (parse_vesteda,         r"/huurwoningen-[a-z-]+/"),
    "vbt":          (parse_vbt,             r"/woning/"),
    "funda":        (None,                  r"/detail/(huur|rent)/"),
    "rentola":      (None,                  r"/(huurwoningen|for-rent)/\d"),
    "generic":      (None,                  r"/(huur|rent|woning|listing)"),
}


def parse_page(site_cfg: dict, url: str, htmltext: str) -> list[Listing]:
    site = site_cfg["name"]
    adapter_name = site_cfg.get("adapter", "generic")
    parser, pattern = ADAPTERS.get(adapter_name, ADAPTERS["generic"])
    soup = BeautifulSoup(htmltext, "lxml")

    results: list[Listing] = []
    if parser:
        results = parser(url, soup, site)
    if not results:
        results = parse_jsonld(url, soup, site)
    if not results:
        results = parse_generic_links(url, soup, site, site_cfg.get("url_pattern") or pattern)

    # Drop obvious non-listings
    results = [r for r in results if len(urlparse(r.url).path.strip("/")) > 8]

    # Dedupe by URL path. The same listing is often linked twice (once from the
    # thumbnail, once from the title), and each copy carries different fields --
    # so merge them instead of throwing one away.
    merged: dict[str, Listing] = {}
    for r in results:
        path = urlparse(r.url).path.rstrip("/")
        if path not in merged:
            merged[path] = r
            continue
        existing = merged[path]
        for fname in ("title", "address", "price", "size_m2", "rooms",
                      "bedrooms", "agent", "image", "raw_text", "fingerprint"):
            if not getattr(existing, fname) and getattr(r, fname):
                setattr(existing, fname, getattr(r, fname))

    final = list(merged.values())
    for l in final:
        if not l.title:  # derive something readable from the URL slug
            slug = urlparse(l.url).path.rstrip("/").rsplit("/", 1)[-1]
            slug = re.sub(r"-[0-9a-f]{16,}$", "", slug)   # drop trailing hash
            l.title = slug.replace("-", " ").title()
    return final


# --------------------------------------------------------------------------
# Fetching
# --------------------------------------------------------------------------

USER_AGENTS = [
    "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 "
    "(KHTML, like Gecko) Chrome/125.0.0.0 Safari/537.36",
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
    "(KHTML, like Gecko) Chrome/125.0.0.0 Safari/537.36",
]


def fetch(url: str, timeout: int = 30) -> Optional[str]:
    headers = {
        "User-Agent": random.choice(USER_AGENTS),
        "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
        "Accept-Language": "nl-NL,nl;q=0.9,en-US;q=0.8,en;q=0.7",
        "Accept-Encoding": "gzip, deflate, br",
        "Upgrade-Insecure-Requests": "1",
        "Sec-Fetch-Dest": "document",
        "Sec-Fetch-Mode": "navigate",
        "Sec-Fetch-Site": "none",
        "Cache-Control": "no-cache",
    }
    kwargs = {"headers": headers, "timeout": timeout}
    if HAVE_CURL_CFFI:
        kwargs["impersonate"] = "chrome"
    try:
        resp = http.get(url, **kwargs)
    except Exception as exc:
        log.warning("fetch failed for %s: %s", url, exc)
        return None
    if resp.status_code != 200:
        log.warning("HTTP %s for %s", resp.status_code, url)
        return None
    return resp.text


# --------------------------------------------------------------------------
# Map area filtering
#
# Listings arrive as addresses, not coordinates, so to test whether one falls
# inside a drawn area we geocode it first. PDOK is the Dutch government's own
# geocoder: free, no API key, no rate limit worth worrying about, and forgiving
# about messy input ("1015 DV Amsterdam" or "Hiraistraat 3 Amsterdam" both work).
#
# Results are cached in SQLite, so each address costs one request ever.
# --------------------------------------------------------------------------

PDOK_URL = "https://api.pdok.nl/bzk/locatieserver/search/v3_1/free"


def geocode_query(l: "Listing") -> str:
    """Build the best address string we can from whatever the scraper got."""
    parts = []
    blob = f"{l.address} {l.raw_text}"
    m = re.search(r"\b(\d{4})\s?([A-Za-z]{2})\b", blob)
    if m:
        parts.append(f"{m.group(1)}{m.group(2).upper()}")   # postcode: most precise

    title = re.sub(r"^(appartement|studio|woning|eengezinswoning|huis|maisonnette|"
                   r"flat|apartment|house|room)\s+", "", l.title or "", flags=re.I)
    parts.append(title)

    city = re.sub(r"\b\d{4}\s?[A-Za-z]{2}\b", "", l.address or "")
    city = re.split(r"[·|(]", city)[0]                       # drop "· 4 woningen", "(Jordaan)"
    city = re.sub(r"-\s*\d+\s*Km\.?", "", city, flags=re.I)  # drop "- 4Km."
    parts.append(city)

    return _clean(" ".join(p for p in parts if p.strip()))[:120]


def geocode(query: str, store: "Store") -> Optional[tuple[float, float]]:
    """Address string -> (lat, lon). None when it can't be resolved."""
    if not query:
        return None
    hit = store.get_geo(query)
    if hit is not None:
        return hit if hit != (None, None) else None

    url = f"{PDOK_URL}?q={quote(query)}&rows=1"
    try:
        kwargs = {"timeout": 15, "headers": {"User-Agent": "huurbot/1.0"}}
        if HAVE_CURL_CFFI:
            kwargs["impersonate"] = "chrome"
        resp = http.get(url, **kwargs)
        time.sleep(0.4)   # PDOK is free but runs a fair-use policy; results are
                          # cached below, so this only costs us on first sight
        docs = resp.json().get("response", {}).get("docs", [])
        if not docs:
            store.set_geo(query, None, None)
            return None
        # centroide_ll looks like "POINT(4.89 52.37)" -- longitude first
        pm = re.search(r"POINT\(([-\d.]+)\s+([-\d.]+)\)", docs[0].get("centroide_ll", ""))
        if not pm:
            store.set_geo(query, None, None)
            return None
        lon, lat = float(pm.group(1)), float(pm.group(2))
        store.set_geo(query, lat, lon)
        return (lat, lon)
    except Exception as exc:
        log.debug("geocode failed for %r: %s", query, exc)
        return None       # deliberately not cached, so a blip can be retried


def point_in_polygon(lat: float, lon: float, poly: list) -> bool:
    """Ray casting. poly is [[lat, lon], ...]."""
    inside = False
    n = len(poly)
    for i in range(n):
        y1, x1 = poly[i][0], poly[i][1]
        y2, x2 = poly[(i + 1) % n][0], poly[(i + 1) % n][1]
        if (y1 > lat) != (y2 > lat):
            xint = (x2 - x1) * (lat - y1) / (y2 - y1) + x1
            if lon < xint:
                inside = not inside
    return inside


def check_area(l: "Listing", areas: list, store: "Store") -> tuple[bool, str]:
    """
    Is this listing inside one of the drawn areas?

    Fails OPEN: if we can't work out where it is, it passes. A geocoder outage
    should never silently stop your alerts.
    """
    if not areas:
        return True, ""
    q = geocode_query(l)
    pos = geocode(q, store)
    if pos is None:
        log.debug("no coordinates for %r -- allowing it through", q)
        return True, ""
    for poly in areas:
        if len(poly) >= 3 and point_in_polygon(pos[0], pos[1], poly):
            return True, ""
    return False, f"outside drawn area ({q})"


# --------------------------------------------------------------------------
# Filtering
# --------------------------------------------------------------------------

def passes_filters(listing: Listing, f: dict) -> tuple[bool, str]:
    if f.get("max_price") and listing.price and listing.price > f["max_price"]:
        return False, f"price {listing.price} > {f['max_price']}"
    if f.get("min_price") and listing.price and listing.price < f["min_price"]:
        return False, f"price {listing.price} < {f['min_price']}"
    if f.get("min_size_m2") and listing.size_m2 and listing.size_m2 < f["min_size_m2"]:
        return False, f"size {listing.size_m2} < {f['min_size_m2']}"
    if f.get("min_rooms") and listing.rooms and listing.rooms < f["min_rooms"]:
        return False, f"rooms {listing.rooms} < {f['min_rooms']}"

    blob = " ".join([listing.title, listing.address, listing.agent, listing.raw_text]).lower()

    # Some sites search by radius and return neighbouring towns. If a listing
    # names no city at all we let it through rather than risk dropping it.
    cities = [c.lower() for c in (f.get("only_cities") or [])]
    if cities:
        place = " ".join([listing.address, listing.url, listing.raw_text]).lower()
        if not any(c in place for c in cities):
            return False, "city not in only_cities"

    for word in (f.get("exclude_keywords") or []):
        if word.lower() in blob:
            return False, f"excluded keyword '{word}'"
    required = f.get("require_any_keywords") or []
    if required and not any(w.lower() in blob for w in required):
        return False, "no required keyword"
    return True, ""


# --------------------------------------------------------------------------
# Storage
# --------------------------------------------------------------------------

class Store:
    def __init__(self, path: Path):
        self.conn = sqlite3.connect(path)
        self.conn.execute("""
            CREATE TABLE IF NOT EXISTS seen (
                key TEXT PRIMARY KEY,
                site TEXT,
                url TEXT,
                title TEXT,
                price INTEGER,
                first_seen TEXT,
                notified INTEGER DEFAULT 0
            )
        """)
        self.conn.execute("""
            CREATE TABLE IF NOT EXISTS geocache (
                query TEXT PRIMARY KEY,
                lat REAL,
                lon REAL,
                looked_up TEXT
            )
        """)
        self.conn.commit()

    def get_geo(self, query: str):
        """(lat, lon), or (None, None) for a known failure, or None if unseen."""
        row = self.conn.execute(
            "SELECT lat, lon FROM geocache WHERE query = ?", (query,)).fetchone()
        return None if row is None else (row[0], row[1])

    def set_geo(self, query: str, lat, lon) -> None:
        self.conn.execute(
            "INSERT OR REPLACE INTO geocache (query, lat, lon, looked_up) VALUES (?,?,?,?)",
            (query, lat, lon, datetime.now(timezone.utc).isoformat()))
        self.conn.commit()

    def is_new(self, listing: Listing) -> bool:
        cur = self.conn.execute("SELECT 1 FROM seen WHERE key = ?", (listing.key,))
        return cur.fetchone() is None

    def record(self, listing: Listing, notified: bool) -> None:
        self.conn.execute(
            "INSERT OR IGNORE INTO seen (key, site, url, title, price, first_seen, notified) "
            "VALUES (?,?,?,?,?,?,?)",
            (listing.key, listing.site, listing.url, listing.title, listing.price,
             datetime.now(timezone.utc).isoformat(), int(notified)),
        )
        self.conn.commit()

    def count(self) -> int:
        return self.conn.execute("SELECT COUNT(*) FROM seen").fetchone()[0]

    # -- state file -------------------------------------------------------
    # A CI runner starts with an empty filesystem, so the "already seen" list
    # has to live in the repo. Committing the SQLite file would work but it's
    # binary: every rewrite stores a whole new copy and the repo balloons.
    # A sorted text file appends a line per listing and git stores just that.

    def export_keys(self, path: Path, prune_days: int = 90) -> int:
        """
        Write the seen-listings state.

        Entries older than prune_days are dropped, otherwise the file grows
        forever -- and with a check every few minutes round the clock, that
        means a steadily bloating repo. Anything that old is long gone from the
        sites anyway, so it can't re-alert. Keep the window well above how long
        a listing actually stays up (weeks, not months) or pruned-but-still-live
        listings would be re-announced.
        """
        cutoff = ""
        if prune_days > 0:
            cutoff = (datetime.now(timezone.utc)
                      - timedelta(days=prune_days)).isoformat()
        rows = self.conn.execute(
            "SELECT key, site, first_seen, url FROM seen ORDER BY key").fetchall()
        kept = [r for r in rows if not cutoff or not r[2] or r[2] >= cutoff]
        with open(path, "w", encoding="utf-8") as fh:
            fh.write("# huurbot seen-listings state. One line per listing.\n")
            for r in kept:
                fh.write("\t".join(str(x or "") for x in r) + "\n")
        dropped = len(rows) - len(kept)
        if dropped:
            log.info("Pruned %d entries older than %d days", dropped, prune_days)
        return len(kept)

    def import_keys(self, path: Path) -> int:
        if not path.exists():
            return 0
        added = 0
        for line in path.read_text(encoding="utf-8").splitlines():
            if not line or line.startswith("#"):
                continue
            parts = line.split("\t")
            if len(parts) < 2:
                continue
            key, site = parts[0], parts[1]
            first_seen = parts[2] if len(parts) > 2 else ""
            url = parts[3] if len(parts) > 3 else ""
            cur = self.conn.execute(
                "INSERT OR IGNORE INTO seen (key, site, url, title, price, first_seen, notified) "
                "VALUES (?,?,?,?,?,?,1)", (key, site, url, "", None, first_seen))
            added += cur.rowcount
        self.conn.commit()
        return added


# --------------------------------------------------------------------------
# Email
# --------------------------------------------------------------------------

def build_email_html(listings: list[Listing]) -> str:
    rows = []
    for l in listings:
        img = (f'<img src="{html.escape(l.image)}" width="150" '
               f'style="border-radius:6px;display:block" alt="">') if l.image else ""
        title = html.escape(l.title or l.address or l.url)
        addr = html.escape(l.address)
        meta = html.escape(l.summary())
        agent = html.escape(l.agent)
        rows.append(f"""
        <tr>
          <td style="padding:12px 10px;vertical-align:top;width:160px">{img}</td>
          <td style="padding:12px 10px;vertical-align:top;font-family:-apple-system,Segoe UI,Helvetica,Arial,sans-serif">
            <a href="{html.escape(l.url)}" style="font-size:16px;font-weight:600;color:#1a4d8f;text-decoration:none">{title}</a>
            <div style="color:#555;font-size:14px;margin-top:4px">{addr}</div>
            <div style="color:#111;font-size:15px;margin-top:6px;font-weight:600">{meta}</div>
            <div style="color:#888;font-size:12px;margin-top:6px">{agent} &middot; {html.escape(l.site)}</div>
          </td>
        </tr>""")

    return f"""<html><body style="background:#f5f5f5;padding:16px;margin:0">
      <div style="max-width:640px;margin:0 auto;background:#fff;border-radius:10px;padding:8px 12px">
        <h2 style="font-family:-apple-system,Segoe UI,Helvetica,Arial,sans-serif;font-size:18px;padding:12px 10px 0">
          {len(listings)} new listing{'s' if len(listings) != 1 else ''}
        </h2>
        <table style="width:100%;border-collapse:collapse">{''.join(rows)}</table>
        <p style="font-family:-apple-system,Segoe UI,Helvetica,Arial,sans-serif;color:#999;font-size:11px;padding:10px">
          Sent by huurbot at {datetime.now().strftime('%Y-%m-%d %H:%M')}
        </p>
      </div></body></html>"""


def send_email(cfg: dict, subject: str, body_html: str, body_text: str) -> None:
    e = cfg["email"]
    # Environment wins over the config file, so the same repo can run in CI
    # (credentials in Secrets) and locally (credentials in config.yaml).
    username = os.environ.get("HUURBOT_SMTP_USERNAME") or e.get("username")
    sender = os.environ.get("HUURBOT_SMTP_USERNAME") or e.get("from_address") or username
    recipients = os.environ.get("HUURBOT_MAIL_TO") or e.get("to_addresses")
    if isinstance(recipients, str):
        recipients = [r.strip() for r in recipients.split(",") if r.strip()]
    if not recipients:
        raise RuntimeError("No recipient. Set HUURBOT_MAIL_TO or email.to_addresses.")

    password = os.environ.get("HUURBOT_SMTP_PASSWORD") or e.get("password")
    if not password:
        raise RuntimeError("No SMTP password. Set HUURBOT_SMTP_PASSWORD or email.password in config.yaml")
    # Google shows app passwords as four space-separated blocks ("abcd efgh ijkl
    # mnop") purely for readability. SMTP rejects the spaces with
    # "535-5.7.8 Username and Password not accepted", so strip them.
    password = password.replace(" ", "").replace("\u00a0", "").strip()

    msg = EmailMessage()
    msg["Subject"] = subject
    msg["From"] = sender
    msg["To"] = ", ".join(recipients)
    msg.set_content(body_text)
    msg.add_alternative(body_html, subtype="html")

    port = int(e.get("smtp_port", 587))
    if port == 465:
        with smtplib.SMTP_SSL(e["smtp_host"], port, timeout=30) as s:
            s.login(username, password)
            s.send_message(msg)
    else:
        with smtplib.SMTP(e["smtp_host"], port, timeout=30) as s:
            s.starttls()
            s.login(username, password)
            s.send_message(msg)
    log.info("Email sent: %s", subject)


# --------------------------------------------------------------------------
# Core check
# --------------------------------------------------------------------------

def paginate(url: str, pages: int) -> list[str]:
    """
    Expand one search URL into pages 1..N.

    Two styles are supported:
      - Put {page} in the URL and it gets substituted:
            https://example.nl/woningen/{page}   ->  /woningen/1, /woningen/2
        Needed for sites that paginate by path rather than query string.
      - Otherwise a ?page=N parameter is appended.

    Some sites keep sort order in the session rather than the URL, so watching
    only page 1 can miss listings. Fetching a couple of pages covers that.
    """
    if "{page}" in url:
        return [url.replace("{page}", str(n)) for n in range(1, max(1, pages) + 1)]
    if pages <= 1:
        return [url]
    out = []
    for n in range(1, pages + 1):
        sep = "&" if urlparse(url).query else "?"
        out.append(f"{url}{sep}page={n}")
    return out


def diagnose_empty(page: str, site_cfg: dict) -> str:
    """
    Work out WHY a page yielded nothing. The three causes need completely
    different fixes, and guessing wastes a lot of time.
    """
    low = page.lower()
    if any(s in low for s in ("just a moment", "cf-browser-verification", "captcha",
                              "verify you are human", "checking your browser")):
        return ("the response is a bot check, so we're being blocked. Slow "
                "interval_minutes down and make sure curl_cffi is installed.")

    soup = BeautifulSoup(page, "lxml")
    links = soup.find_all("a", href=True)
    adapter = site_cfg.get("adapter", "generic")
    pattern = site_cfg.get("url_pattern") or ADAPTERS.get(adapter, ADAPTERS["generic"])[1]
    try:
        matched = sum(1 for a in links if re.search(pattern, a["href"]))
    except re.error:
        matched = 0

    if not links:
        return "the page came back essentially empty -- likely wrong URL or a redirect."
    if matched == 0:
        return (f"the page loaded fine ({len(links)} links) but none look like listings "
                f"(pattern {pattern!r}). This is usually the WRONG PAGE -- a city "
                f"landing/marketing page rather than the actual search results. "
                f"Open the URL in a browser and check you see listing cards.")
    return (f"found {matched} listing-shaped links but couldn't parse them -- "
            f"the markup probably changed. Run with --dump and check the adapter.")


def run_check(cfg: dict, store: Store, notify: bool = True, dump: bool = False) -> list[Listing]:
    new_hits: list[Listing] = []
    filters = cfg.get("filters", {})

    for site_cfg in cfg["sites"]:
        if not site_cfg.get("enabled", True):
            continue
        name = site_cfg["name"]
        pages = int(site_cfg.get("pages", 1))
        urls = [u for base in site_cfg["search_urls"] for u in paginate(base, pages)]
        for url in urls:
            page = fetch(url)
            if page is None:
                continue

            if dump:
                DEBUG_DIR.mkdir(exist_ok=True)
                stamp = datetime.now().strftime("%H%M%S")
                (DEBUG_DIR / f"{name}_{stamp}.html").write_text(page, encoding="utf-8")
                log.info("dumped %s bytes -> debug/%s_%s.html", len(page), name, stamp)

            listings = parse_page(site_cfg, url, page)
            log.info("%-14s %3d listings parsed", name, len(listings))
            if not listings:
                log.warning("%s returned 0 listings from %s\n    -> %s",
                            name, url, diagnose_empty(page, site_cfg))

            for listing in listings:
                if not store.is_new(listing):
                    continue
                ok, reason = passes_filters(listing, filters)
                if ok:
                    # Geocoding costs an HTTP request, so only for listings
                    # that already cleared the cheap filters.
                    ok, reason = check_area(listing, filters.get("areas") or [], store)
                store.record(listing, notified=ok and notify)
                if not ok:
                    log.debug("filtered out %s (%s)", listing.url, reason)
                    continue
                new_hits.append(listing)

            time.sleep(random.uniform(2, 5))  # be polite between requests

    if new_hits and notify:
        text = "\n\n".join(f"{l.title}\n{l.summary()}\n{l.url}" for l in new_hits)
        subject = cfg["email"].get("subject_prefix", "[huurbot]") + \
            f" {len(new_hits)} new listing{'s' if len(new_hits) != 1 else ''}"
        if len(new_hits) == 1:
            subject += f" - {new_hits[0].title[:60]}"
        try:
            send_email(cfg, subject, build_email_html(new_hits), text)
        except Exception as exc:
            log.error("FAILED to send email: %s", exc)

    return new_hits


def in_quiet_hours(cfg: dict) -> bool:
    q = cfg.get("quiet_hours")
    if not q:
        return False
    hour = datetime.now().hour
    start, end = int(q["start"]), int(q["end"])
    return start <= hour < end if start < end else (hour >= start or hour < end)


# --------------------------------------------------------------------------
# CLI
# --------------------------------------------------------------------------

def load_config(path: Path) -> dict:
    if not path.exists():
        sys.exit(f"Config not found: {path}\nCopy config.example.yaml to config.yaml and edit it.")
    with open(path, encoding="utf-8") as fh:
        cfg = yaml.safe_load(fh)
    for required in ("sites", "email"):
        if required not in cfg:
            sys.exit(f"config.yaml is missing the '{required}' section")
    return cfg


def main() -> None:
    ap = argparse.ArgumentParser(description="Monitor Dutch rental sites and email new listings.")
    ap.add_argument("--config", default=str(BASE_DIR / "config.yaml"))
    ap.add_argument("--once", action="store_true", help="run one check, then exit")
    ap.add_argument("--seed", action="store_true", help="mark current listings as seen, no email")
    ap.add_argument("--test-email", action="store_true", help="send a test email and exit")
    ap.add_argument("--check-config", action="store_true", help="validate config and exit")
    ap.add_argument("--dump", action="store_true", help="save fetched HTML into debug/")
    ap.add_argument("--prune-days", type=int, default=90, metavar="N",
                    help="drop state entries older than N days (0 = keep all). "
                         "Must exceed how long a listing stays live, or old-but-"
                         "still-listed homes get re-announced. Default 90.")
    ap.add_argument("--state-file", metavar="PATH",
                    help="load/save seen listings from a text file (for CI, where "
                         "the filesystem is wiped between runs)")
    ap.add_argument("-v", "--verbose", action="store_true")
    args = ap.parse_args()

    logging.basicConfig(
        level=logging.DEBUG if args.verbose else logging.INFO,
        format="%(asctime)s  %(levelname)-7s %(message)s",
        datefmt="%Y-%m-%d %H:%M:%S",
        handlers=[logging.StreamHandler(sys.stdout),
                  logging.FileHandler(BASE_DIR / "huurbot.log", encoding="utf-8")],
    )

    cfg = load_config(Path(args.config))
    store = Store(DB_PATH)

    state = Path(args.state_file) if args.state_file else None
    if state:
        n = store.import_keys(state)
        log.info("Loaded %d previously-seen listings from %s", n, state)

    if not HAVE_CURL_CFFI:
        log.warning("curl_cffi not installed -- falling back to `requests`, which "
                    "more sites will block. Install it: pip install curl_cffi")

    if args.check_config:
        enabled = [s["name"] for s in cfg["sites"] if s.get("enabled", True)]
        e = cfg.get("email", {})
        to = os.environ.get("HUURBOT_MAIL_TO") or e.get("to_addresses") or "(not set)"
        user = os.environ.get("HUURBOT_SMTP_USERNAME") or e.get("username") or "(not set)"
        has_pw = bool(os.environ.get("HUURBOT_SMTP_PASSWORD") or e.get("password"))
        print(f"Sites enabled : {', '.join(enabled) or '(none!)'}")
        print(f"Filters       : {json.dumps(cfg.get('filters', {}), indent=2)}")
        print(f"Email from    : {user}")
        print(f"Email to      : {to}")
        print(f"Password set  : {'yes' if has_pw else 'NO -- set HUURBOT_SMTP_PASSWORD'}")
        print(f"Interval      : {cfg.get('interval_minutes', 5)} min")
        print(f"Listings known: {store.count()}")
        return

    if args.test_email:
        demo = Listing(site="test", url="https://example.com/listing/1",
                       title="Test listing - Prinsengracht 123",
                       address="1015 Amsterdam, Jordaan", price=1750,
                       size_m2=68, rooms=3, agent="Test Makelaardij")
        send_email(cfg, "[huurbot] test email", build_email_html([demo]),
                   "If you can read this, email works.")
        print("Test email sent. Check your inbox (and spam folder).")
        return

    if args.seed:
        found = run_check(cfg, store, notify=False, dump=args.dump)
        if state:
            print(f"Wrote {store.export_keys(state, args.prune_days)} entries to {state}")
        print(f"Seeded. {store.count()} listings marked as already seen. "
              f"From now on you'll only hear about genuinely new ones.")
        return

    if args.once:
        hits = run_check(cfg, store, notify=True, dump=args.dump)
        if state:
            store.export_keys(state, args.prune_days)
        print(f"Done. {len(hits)} new listing(s).")
        return

    interval = int(cfg.get("interval_minutes", 5)) * 60
    jitter = int(cfg.get("jitter_seconds", 90))
    log.info("Starting. Checking every ~%d min. Ctrl-C to stop.", interval // 60)
    log.info("Known listings in database: %d", store.count())

    consecutive_errors = 0
    while True:
        try:
            if in_quiet_hours(cfg):
                log.info("Quiet hours - skipping this check.")
            else:
                hits = run_check(cfg, store, notify=True, dump=False)
                if hits:
                    log.info(">>> %d new listing(s) emailed", len(hits))
            consecutive_errors = 0
        except KeyboardInterrupt:
            log.info("Stopped by user.")
            break
        except Exception as exc:
            consecutive_errors += 1
            log.exception("Check failed (%d in a row): %s", consecutive_errors, exc)

        # Back off if things are consistently broken
        wait = interval * min(2 ** consecutive_errors, 8) if consecutive_errors else interval
        wait += random.uniform(-jitter, jitter)
        time.sleep(max(30, wait))


if __name__ == "__main__":
    main()
