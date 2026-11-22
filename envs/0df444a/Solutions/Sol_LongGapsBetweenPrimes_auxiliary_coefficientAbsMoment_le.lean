-- Prove2me | solution 1 for LongGapsBetweenPrimes.auxiliary_coefficientAbsMoment_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:01:58.689691+00:00
-- url     : https://prove2.me/submissions/98c962d9-575d-4c7f-b425-2d76b6a8052e

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_coefficientAbsMoment_le
import Theorems.Thm_LongGapsBetweenPrimes_divisorEulerMoment_zero_le
import Theorems.Thm_LongGapsBetweenPrimes_auxiliary_divisorEulerMoment_tilt

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {Z Y : ℕ} (hZY : Z ≤ Y) (hZ : 2 ≤ Z)
    (hlogZ : 1 ≤ Real.log Z) (hP : 1 < auxiliaryProduct Z Y)
    {b γ : ℝ} (hb : 0 < b) (hB : b ≤ normalizer (auxiliaryProduct Z Y))
    (hγ : 0 ≤ γ) (hscale : γ * Real.log Y ≤ 2) :
    coefficientAbsMoment (auxiliaryProduct Z Y) γ ≤ absoluteMomentBound b := by
  have hY : 1 < Y := by omega
  have hlogY : 1 ≤ Real.log (Y : ℝ) :=
    hlogZ.trans (Real.log_le_log (by exact_mod_cast (by omega : 0 < Z))
      (by exact_mod_cast hZY))
  have hlogYpos : 0 < Real.log (Y : ℝ) := zero_lt_one.trans_le hlogY
  have hYE : (Y : ℝ) ^ γ ≤ Real.exp 2 := by
    rw [Real.rpow_def_of_pos (by exact_mod_cast (by omega : 0 < Y))]
    exact Real.exp_le_exp.mpr (by simpa [mul_comm] using hscale)
  have hzero : divisorEulerMoment (auxiliaryProduct Z Y) 0 ≤
      2 * Real.exp 6 * Real.log Y := by
    calc
      _ ≤ Real.exp 6 * (1 + Real.log Y) / Real.log Z :=
        divisorEulerMoment_zero_le hZY hZ
      _ ≤ Real.exp 6 * (1 + Real.log Y) := div_le_self (by positivity) hlogZ
      _ ≤ 2 * Real.exp 6 * Real.log Y := by nlinarith [Real.exp_pos 6]
  have hmoment : divisorEulerMoment (auxiliaryProduct Z Y) γ ≤
      (2 * Real.exp 6 * Real.exp (6 * Real.exp 2)) * Real.log Y := by
    calc
      _ ≤ divisorEulerMoment (auxiliaryProduct Z Y) 0 * Real.exp (6 * Real.exp 2) :=
        auxiliary_divisorEulerMoment_tilt (hZ.trans hZY) hγ hscale
      _ ≤ (2 * Real.exp 6 * Real.log Y) * Real.exp (6 * Real.exp 2) :=
        mul_le_mul_of_nonneg_right hzero (Real.exp_nonneg _)
      _ = _ := by ring
  calc
    _ ≤ Real.exp 2 + divisorEulerMoment (auxiliaryProduct Z Y) γ /
        (normalizer (auxiliaryProduct Z Y) * Real.log Y) :=
      coefficientAbsMoment_le hP hY hγ hYE
    _ ≤ Real.exp 2 +
        ((2 * Real.exp 6 * Real.exp (6 * Real.exp 2)) * Real.log Y) /
          (b * Real.log Y) := by
      gcongr
    _ = absoluteMomentBound b := by
      unfold absoluteMomentBound
      rw [mul_div_mul_right _ _ hlogYpos.ne']
end LongGapsBetweenPrimes
