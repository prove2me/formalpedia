-- Prove2me | solution 1 for LongGapsBetweenPrimes.abs_residueFactor_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:43:25.041351+00:00
-- url     : https://prove2.me/submissions/ba78edb7-acb0-4655-b3cf-23936bad845a

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {p : ℕ} (hp : 1 < p) (a t : Fin p) :
    |residueFactor a t| ≤ 1 := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast Nat.succ_le_of_lt hp
  unfold residueFactor
  split_ifs
  · norm_num
  · rw [abs_of_nonneg (div_nonneg zero_le_one (by linarith))]
    exact (div_le_one (by linarith)).mpr (by linarith)
end LongGapsBetweenPrimes
