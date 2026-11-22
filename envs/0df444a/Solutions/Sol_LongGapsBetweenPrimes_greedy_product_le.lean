-- Prove2me | solution 1 for LongGapsBetweenPrimes.greedy_product_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:13:18.213159+00:00
-- url     : https://prove2.me/submissions/e564cbd6-5fce-421c-ba46-82d546ca4230

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_log_le_eulerProduct_one
import Theorems.Thm_LongGapsBetweenPrimes_eulerProduct_one_le
import Theorems.Thm_LongGapsBetweenPrimes_auxiliaryPrimes_prime
import Theorems.Thm_LongGapsBetweenPrimes_auxiliary_euler_factorization

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {W Z : ℕ} (hW : 2 ≤ W) (hWZ : W ≤ Z) :
    (∏ p ∈ auxiliaryPrimes W Z, (1 - 1 / (p : ℝ))) ≤
      Real.exp 6 * (1 + Real.log W) / Real.log Z := by
  have hprod : 0 < ∏ p ∈ auxiliaryPrimes W Z, (1 - 1 / (p : ℝ)) := by
    apply Finset.prod_pos
    intro p hp
    simpa only [one_div] using sub_pos.mpr
      (inv_lt_one_of_one_lt₀ (by exact_mod_cast (auxiliaryPrimes_prime hp).one_lt))
  have hfactor := auxiliary_euler_factorization hWZ 1
  simp only [Real.rpow_neg_one] at hfactor
  rw [Finset.prod_inv_distrib, inv_mul_eq_div] at hfactor
  simp only [← one_div] at hfactor
  have hcancel := (div_eq_iff hprod.ne').mp hfactor
  have hlog : 0 < Real.log (Z : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < Z))
  apply (le_div_iff₀ hlog).mpr
  calc
    _ ≤ (∏ p ∈ auxiliaryPrimes W Z, (1 - 1 / (p : ℝ))) * eulerProduct Z 1 :=
      mul_le_mul_of_nonneg_left (log_le_eulerProduct_one Z) hprod.le
    _ = eulerProduct W 1 := (mul_comm _ _).trans hcancel.symm
    _ ≤ Real.exp 6 * (1 + Real.log W) := eulerProduct_one_le hW
end LongGapsBetweenPrimes
