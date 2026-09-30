-- Prove2me | solution 1 for NonuniformCompetitive.Triangle345.lp_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T08:29:37.943012+00:00
-- url     : https://prove2.me/submissions/cd87de92-94b4-42fa-bb78-16f8323cbadd

import Mathlib.Tactic

theorem solution (π₁ π₂ π₃ π₄ π₅ π₆ π₇ π₈ π₉ Φab Φac Φbc α : ℝ)
    -- phase 1: {a,b}, requests ca, final {a,c}, opt 4
    (h1 : 8 - 4 * π₁ ≤ 4 * α + Φab - Φac)
    -- phase 2: {a,b}, requests cbaba, final {a,b}, opt 8
    (h2 : 16 + 2 * π₁ - 4 * π₂ - 2 * π₃ - 4 * π₄ ≤ 8 * α + Φab - Φab)
    -- phase 3: {a,b}, requests cbabca, final {a,c}, opt 12
    (h3 : 14 + 2 * π₁ - 4 * π₂ - 2 * π₃ + 6 * π₄ - 4 * π₅ ≤ 12 * α + Φab - Φac)
    -- phase 4: {a,b}, requests cbabcb, final {b,c}, opt 11
    (h4 : 11 + 2 * π₁ - 4 * π₂ - 2 * π₃ + 6 * π₄ + 2 * π₅ ≤ 11 * α + Φab - Φbc)
    -- phase 5: {a,b}, requests cbac, final {a,c}, opt 8
    (h5 : 8 + 2 * π₁ - 4 * π₂ + 6 * π₃ ≤ 8 * α + Φab - Φac)
    -- phase 6: {a,b}, requests cbc, final {b,c}, opt 5
    (h6 : 5 + 2 * π₁ + 6 * π₂ ≤ 5 * α + Φab - Φbc)
    -- phase 7: {a,c}, requests bab, final {a,b}, opt 4
    (h7 : 10 - 4 * π₆ - 2 * π₇ ≤ 4 * α + Φac - Φab)
    -- phase 8: {a,c}, requests bac, final {a,c}, opt 6
    (h8 : 6 - 4 * π₆ + 6 * π₇ ≤ 6 * α + Φac - Φac)
    -- phase 9: {a,c}, requests bc, final {b,c}, opt 3
    (h9 : 3 + 6 * π₆ ≤ 3 * α + Φac - Φbc)
    -- phase 10: {b,c}, requests aba, final {a,b}, opt 5
    (h10 : 11 - 2 * π₈ - 4 * π₉ ≤ 5 * α + Φbc - Φab)
    -- phase 11: {b,c}, requests abc, final {b,c}, opt 6
    (h11 : 6 - 2 * π₈ + 6 * π₉ ≤ 6 * α + Φbc - Φbc)
    -- phase 12: {b,c}, requests ac, final {a,c}, opt 3
    (h12 : 3 + 6 * π₈ ≤ 3 * α + Φbc - Φac) :
    (1652 / 1069 : ℝ) ≤ α := by
  linarith
