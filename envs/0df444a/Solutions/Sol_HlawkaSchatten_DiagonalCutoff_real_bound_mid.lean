-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff.real_bound_mid
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-28T01:12:15.856398+00:00
-- url     : https://prove2.me/submissions/93a90deb-b246-4856-9ff9-2e5bf45dff5d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff_real_bound8
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff_real_bound_below8

open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem solution :
    ∀ p : ℝ, 2 ≤ p → p ≤ 16 → ∀ n : ℕ,
      HasHlawkaConstant (lpNorm p : (Fin n → ℝ) → ℝ)
        (cyclicConstant p) := by
  intro p hp2 hp16 n
  by_cases h : p ≤ 8
  · exact HlawkaSchatten.DiagonalCutoff.real_bound_below8 p hp2 h n
  · push Not at h
    exact HlawkaSchatten.DiagonalCutoff.real_bound8 p (le_of_lt h) n
