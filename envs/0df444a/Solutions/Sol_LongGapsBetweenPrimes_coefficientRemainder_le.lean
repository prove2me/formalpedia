-- Prove2me | solution 1 for LongGapsBetweenPrimes.coefficientRemainder_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:09:22.90588+00:00
-- url     : https://prove2.me/submissions/3d195a13-3dde-4da4-a652-f0ecc200516f

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_coefficient_noncoprime_le
import Theorems.Thm_LongGapsBetweenPrimes_sum_primeFactors_inv_le
import Theorems.Thm_LongGapsBetweenPrimes_coefficient_tail_le
import Theorems.Thm_LongGapsBetweenPrimes_coefficientRemainder_le_tail_add_overlap

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {P m : ℕ} {β C D M : ℝ}
    (h : CoefficientEstimates P β C) (hβ : 0 ≤ β) (hm : m ∣ P)
    (hcut : (m : ℝ) ≤ D) (hM : 0 < M)
    (hmin : ∀ p ∈ P.primeFactors, M ≤ (p : ℝ)) :
    coefficientRemainder P m D ≤ C * ((m : ℝ) / D) ^ β +
      4 * Real.log D / (M * Real.log 2) := by
  have hm0 : 0 < m := Nat.pos_of_mem_divisors
    (Nat.mem_divisors.mpr ⟨hm, h.squarefree.ne_zero⟩)
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm0
  have hv : 1 ≤ D / m := (le_div_iff₀ hmR).mpr (by simpa using hcut)
  apply (coefficientRemainder_le_tail_add_overlap h.one_lt hm0 hcut).trans
  apply add_le_add
  · calc
      _ ≤ (D / m) ^ (-β) * coefficientAbsMoment P β := coefficient_tail_le hv hβ
      _ ≤ (D / m) ^ (-β) * C := mul_le_mul_of_nonneg_left
        (h.absMoment_le β hβ (by linarith)) (Real.rpow_nonneg (by positivity) _)
      _ = C * ((m : ℝ) / D) ^ β := by
        rw [Real.rpow_neg (by positivity), ← Real.inv_rpow (by positivity), inv_div]
        exact mul_comm _ _
  · apply (coefficient_noncoprime_le h.one_lt h.squarefree hm h.abs_le_one).trans
    apply (sum_primeFactors_inv_le h.squarefree hm hM hmin).trans
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.log_le_log hmR hcut) (by norm_num)) (by positivity)
end LongGapsBetweenPrimes
