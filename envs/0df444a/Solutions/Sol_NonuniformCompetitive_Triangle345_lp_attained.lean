-- Prove2me | solution 1 for NonuniformCompetitive.Triangle345.lp_attained
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T08:30:33.257265+00:00
-- url     : https://prove2.me/submissions/9f84357d-1262-4c8b-8c8c-8c3fa6bd99ab

import Mathlib.Tactic

theorem solution :
    let π₁ : ℝ := 2161 / 3207
    let π₂ : ℝ := 169 / 1069
    let π₃ : ℝ := 1481 / 3207
    let π₄ : ℝ := 2749 / 3207
    let π₅ : ℝ := 1016 / 3207
    let π₆ : ℝ := 371 / 1069
    let π₇ : ℝ := 2491 / 3207
    let π₈ : ℝ := 212 / 1069
    let π₉ : ℝ := 1961 / 3207
    let α : ℝ := 1652 / 1069
    (0 ≤ π₁ ∧ π₁ ≤ 1) ∧ (0 ≤ π₂ ∧ π₂ ≤ 1) ∧ (0 ≤ π₃ ∧ π₃ ≤ 1) ∧
    (0 ≤ π₄ ∧ π₄ ≤ 1) ∧ (0 ≤ π₅ ∧ π₅ ≤ 1) ∧ (0 ≤ π₆ ∧ π₆ ≤ 1) ∧
    (0 ≤ π₇ ∧ π₇ ≤ 1) ∧ (0 ≤ π₈ ∧ π₈ ≤ 1) ∧ (0 ≤ π₉ ∧ π₉ ≤ 1) ∧
    ∃ Φab Φac Φbc : ℝ,
      -- phase 1: {a,b}, requests ca, final {a,c}, opt 4
      8 - 4 * π₁ ≤ 4 * α + Φab - Φac ∧
      -- phase 2: {a,b}, requests cbaba, final {a,b}, opt 8
      16 + 2 * π₁ - 4 * π₂ - 2 * π₃ - 4 * π₄ ≤ 8 * α + Φab - Φab ∧
      -- phase 3: {a,b}, requests cbabca, final {a,c}, opt 12
      14 + 2 * π₁ - 4 * π₂ - 2 * π₃ + 6 * π₄ - 4 * π₅ ≤ 12 * α + Φab - Φac ∧
      -- phase 4: {a,b}, requests cbabcb, final {b,c}, opt 11
      11 + 2 * π₁ - 4 * π₂ - 2 * π₃ + 6 * π₄ + 2 * π₅ ≤ 11 * α + Φab - Φbc ∧
      -- phase 5: {a,b}, requests cbac, final {a,c}, opt 8
      8 + 2 * π₁ - 4 * π₂ + 6 * π₃ ≤ 8 * α + Φab - Φac ∧
      -- phase 6: {a,b}, requests cbc, final {b,c}, opt 5
      5 + 2 * π₁ + 6 * π₂ ≤ 5 * α + Φab - Φbc ∧
      -- phase 7: {a,c}, requests bab, final {a,b}, opt 4
      10 - 4 * π₆ - 2 * π₇ ≤ 4 * α + Φac - Φab ∧
      -- phase 8: {a,c}, requests bac, final {a,c}, opt 6
      6 - 4 * π₆ + 6 * π₇ ≤ 6 * α + Φac - Φac ∧
      -- phase 9: {a,c}, requests bc, final {b,c}, opt 3
      3 + 6 * π₆ ≤ 3 * α + Φac - Φbc ∧
      -- phase 10: {b,c}, requests aba, final {a,b}, opt 5
      11 - 2 * π₈ - 4 * π₉ ≤ 5 * α + Φbc - Φab ∧
      -- phase 11: {b,c}, requests abc, final {b,c}, opt 6
      6 - 2 * π₈ + 6 * π₉ ≤ 6 * α + Φbc - Φbc ∧
      -- phase 12: {b,c}, requests ac, final {a,c}, opt 3
      3 + 6 * π₈ ≤ 3 * α + Φbc - Φac := by
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num, 0, (2812:ℝ)/3207, (1381:ℝ)/3207, ?_⟩
  norm_num
