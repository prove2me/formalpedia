-- Prove2me | solution 1 for LongGapsBetweenPrimes.auxiliary_coefficientAbsMoment_control
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:03:46.324166+00:00
-- url     : https://prove2.me/submissions/91b18e76-20e7-416d-bc61-181fc0e152cd

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_coefficientControl_pos
import Theorems.Thm_LongGapsBetweenPrimes_auxiliary_coefficientAbsMoment_le

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {Z Y : ℕ} (hZY : Z ≤ Y) (hZ : 2 ≤ Z)
    (hlogZ : 1 ≤ Real.log Z) (hP : 1 < auxiliaryProduct Z Y)
    {b γ : ℝ} (hb : 0 < b) (hB : b ≤ normalizer (auxiliaryProduct Z Y))
    (hγ : 0 ≤ γ) (hscale : γ * Real.log Y ≤ 2) :
    coefficientAbsMoment (auxiliaryProduct Z Y) γ ≤
      coefficientControl b * normalizer (auxiliaryProduct Z Y) := by
  calc
    _ ≤ absoluteMomentBound b := auxiliary_coefficientAbsMoment_le hZY hZ hlogZ hP hb hB hγ hscale
    _ = coefficientControl b * b := by
      rw [coefficientControl, div_mul_cancel₀ _ (ne_of_gt hb)]
    _ ≤ _ := mul_le_mul_of_nonneg_left hB (coefficientControl_pos hb).le
end LongGapsBetweenPrimes
