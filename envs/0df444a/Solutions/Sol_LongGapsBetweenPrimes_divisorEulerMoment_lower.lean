-- Prove2me | solution 1 for LongGapsBetweenPrimes.divisorEulerMoment_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:58:23.455168+00:00
-- url     : https://prove2.me/submissions/c0341c32-bde8-4805-b44d-65ff4a09decf

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_eulerProduct_antitone
import Theorems.Thm_LongGapsBetweenPrimes_divisorEulerMoment_ge_eulerProduct
import Theorems.Thm_LongGapsBetweenPrimes_eulerProduct_ge_one_div_two_mul
import Theorems.Thm_LongGapsBetweenPrimes_divisorEulerMoment_nonneg

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {Z Y : ℕ} (hZY : Z ≤ Y) {t A : ℝ}
    (ht : 0 < t) (hA : 0 < A) (hZA : eulerProduct Z 1 ≤ A)
    (hscale : 1 ≤ t * Real.log ((Y : ℝ) + 1)) :
    1 / (2 * t * A) ≤ divisorEulerMoment (auxiliaryProduct Z Y) (-t) := by
  have hZ := (eulerProduct_antitone Z (by norm_num : (0 : ℝ) < 1)
    (by linarith : 1 ≤ 1 + t)).trans hZA
  have h := (eulerProduct_ge_one_div_two_mul Y ht hscale).trans
    ((divisorEulerMoment_ge_eulerProduct hZY ht).trans
      (mul_le_mul_of_nonneg_left hZ (divisorEulerMoment_nonneg _ _)))
  calc
    1 / (2 * t * A) = (1 / (2 * t)) / A := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ ≤ divisorEulerMoment (auxiliaryProduct Z Y) (-t) := (div_le_iff₀ hA).mpr h
end LongGapsBetweenPrimes
