-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff.real_bound_below8
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-28T01:18:33.594414+00:00
-- url     : https://prove2.me/submissions/980b1993-e3b5-4cff-b2a1-748fe6a7de86
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff_real_bound6
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff_real_bound_below6

open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem solution :
    ∀ p : ℝ, 2 ≤ p → p ≤ 8 → ∀ n : ℕ,
      HasHlawkaConstant (lpNorm p : (Fin n → ℝ) → ℝ)
        (cyclicConstant p) := by
  intro p hp2 hp8 n
  by_cases h : p ≤ 6
  · exact HlawkaSchatten.DiagonalCutoff.real_bound_below6 p hp2 h n
  · push Not at h
    exact HlawkaSchatten.DiagonalCutoff.real_bound6 p (le_of_lt h) n
