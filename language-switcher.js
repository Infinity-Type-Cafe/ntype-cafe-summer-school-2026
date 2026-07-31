(() => {
  "use strict";

  const basePath = "/ntype-cafe-summer-school-2026";
  const chinesePath = `${basePath}/`;
  const englishPath = `${basePath}/en/`;
  const chineseArticlePath = `${basePath}/2026/06/01/introduction2026/`;
  const storageKey = "ntype-cafe-language";
  const pathname = window.location.pathname;
  const englishPathWithoutSlash = englishPath.slice(0, -1);
  const isEnglishPage =
    pathname === englishPathWithoutSlash ||
    pathname === englishPath ||
    pathname.startsWith(englishPath);

  let savedLanguage = null;
  try {
    savedLanguage = window.localStorage.getItem(storageKey);
  } catch (_) {
    // The switch still works when storage is unavailable.
  }

  const browserLanguages =
    navigator.languages && navigator.languages.length
      ? navigator.languages
      : [navigator.language || "en"];
  const browserPrefersChinese = String(browserLanguages[0])
    .toLowerCase()
    .startsWith("zh");
  const hasSavedLanguage = savedLanguage === "zh" || savedLanguage === "en";
  const preferredLanguage =
    hasSavedLanguage
      ? savedLanguage
      : browserPrefersChinese
        ? "zh"
        : "en";

  const isChineseLandingPage =
    pathname === basePath ||
    pathname === chinesePath ||
    pathname === chineseArticlePath;

  if (preferredLanguage === "en" && isChineseLandingPage) {
    window.location.replace(englishPath);
    return;
  }

  if (
    hasSavedLanguage &&
    preferredLanguage === "zh" &&
    isEnglishPage
  ) {
    window.location.replace(chinesePath);
    return;
  }

  document.documentElement.lang = isEnglishPage ? "en" : "zh-CN";

  const remember = (language) => {
    try {
      window.localStorage.setItem(storageKey, language);
    } catch (_) {
      // Navigation remains functional without persistent storage.
    }
  };

  const mountSwitcher = () => {
    if (!document.body || document.querySelector(".language-switcher")) {
      return;
    }

    const nav = document.createElement("nav");
    nav.className = "language-switcher";
    nav.setAttribute("aria-label", "Language / 语言");

    const chineseLink = document.createElement("a");
    chineseLink.href = chinesePath;
    chineseLink.textContent = "中文";
    chineseLink.lang = "zh-CN";
    chineseLink.addEventListener("click", () => remember("zh"));

    const englishLink = document.createElement("a");
    englishLink.href = englishPath;
    englishLink.textContent = "English";
    englishLink.lang = "en";
    englishLink.addEventListener("click", () => remember("en"));

    const activeLink = isEnglishPage ? englishLink : chineseLink;
    activeLink.classList.add("is-active");
    activeLink.setAttribute("aria-current", "page");

    nav.append(chineseLink, englishLink);
    document.body.appendChild(nav);
  };

  if (document.readyState === "loading") {
    document.addEventListener("DOMContentLoaded", mountSwitcher, { once: true });
  } else {
    mountSwitcher();
  }
})();
