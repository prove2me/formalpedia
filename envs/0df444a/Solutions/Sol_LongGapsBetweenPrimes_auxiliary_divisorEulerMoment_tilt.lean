-- Prove2me | solution 1 for LongGapsBetweenPrimes.auxiliary_divisorEulerMoment_tilt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:59:45.170743+00:00
-- url     : https://prove2.me/submissions/1029b5c5-7594-4376-9ec4-a63f5829c579

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_sum_prime_log_div_le
import Theorems.Thm_LongGapsBetweenPrimes_auxiliaryPrimes_prime
import Theorems.Thm_LongGapsBetweenPrimes_mem_auxiliaryPrimes
import Theorems.Thm_LongGapsBetweenPrimes_divisorEulerMoment_nonneg
import Theorems.Thm_LongGapsBetweenPrimes_divisorEulerMoment_tilt

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {Z Y : ℕ} (hY : 2 ≤ Y)
    {γ : ℝ} (hγ : 0 ≤ γ) (hscale : γ * Real.log Y ≤ 2) :
    divisorEulerMoment (auxiliaryProduct Z Y) γ ≤
      divisorEulerMoment (auxiliaryProduct Z Y) 0 * Real.exp (6 * Real.exp 2) := by
  have hYr : (2 : ℝ) ≤ Y := by exact_mod_cast hY
  have hYE : (Y : ℝ) ^ γ ≤ Real.exp 2 := by
    rw [Real.rpow_def_of_pos (by linarith)]
    exact Real.exp_le_exp.mpr (by linarith [hscale])
  have hlog4 : Real.log 4 ≤ 2 * Real.log Y := by
    simpa only [Real.log_pow, Nat.cast_ofNat] using
      Real.log_le_log (by norm_num : (0 : ℝ) < 4)
        (show (4 : ℝ) ≤ (Y : ℝ) ^ 2 by nlinarith)
  have hsum : (∑ p ∈ auxiliaryPrimes Z Y, Real.log p / p) ≤ 3 * Real.log Y := by
    calc
      _ ≤ ∑ p ∈ Y.primesLE, Real.log p / p :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.sdiff_subset)
          (fun p hp _ => div_nonneg (Nat.mem_primesLE.mp hp).2.log_pos.le
            (Nat.cast_nonneg p))
      _ ≤ 3 * Real.log Y := by
        linarith [sum_prime_log_div_le (by omega : 1 ≤ Y)]
  have hcost : γ * (∑ p ∈ auxiliaryPrimes Z Y, Real.log p / p) ≤ 6 := by
    nlinarith [mul_le_mul_of_nonneg_left hsum hγ]
  calc
    _ ≤ divisorEulerMoment (auxiliaryProduct Z Y) 0 *
        Real.exp (Real.exp 2 * γ * ∑ p ∈ auxiliaryPrimes Z Y, Real.log p / p) :=
      divisorEulerMoment_tilt (auxiliaryPrimes Z Y) (fun _ hp => auxiliaryPrimes_prime hp)
        hγ (fun p hp => (Real.rpow_le_rpow (Nat.cast_nonneg p)
          (by exact_mod_cast (mem_auxiliaryPrimes.mp hp).2.2) hγ).trans hYE)
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by
        nlinarith [mul_le_mul_of_nonneg_left hcost (Real.exp_nonneg 2)]))
      (divisorEulerMoment_nonneg _ _)
end LongGapsBetweenPrimes
