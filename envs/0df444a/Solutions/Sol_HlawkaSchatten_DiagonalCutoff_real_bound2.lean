-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff.real_bound2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-28T01:02:15.864254+00:00
-- url     : https://prove2.me/submissions/38a2d670-4326-4770-a18b-463b56830e0b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff_real_bound_mid
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff_real_bound16

open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem solution :
    ∀ p : ℝ, 2 ≤ p → ∀ n : ℕ,
      HasHlawkaConstant (lpNorm p : (Fin n → ℝ) → ℝ)
        (cyclicConstant p) := by
  intro p hp n
  by_cases h : p ≤ 16
  · exact HlawkaSchatten.DiagonalCutoff.real_bound_mid p hp h n
  · push Not at h
    exact HlawkaSchatten.DiagonalCutoff.real_bound16 p (le_of_lt h) n
