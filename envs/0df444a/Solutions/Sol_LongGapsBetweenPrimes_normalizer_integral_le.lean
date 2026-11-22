-- Prove2me | solution 1 for LongGapsBetweenPrimes.normalizer_integral_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:57:31.227955+00:00
-- url     : https://prove2.me/submissions/4ad827cc-4a5c-410d-b087-845b3528fdfb

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_one_lt_of_mem_divisors_erase_one
import Theorems.Thm_LongGapsBetweenPrimes_integral_exp_decay_le

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {P : ℕ} (hP : P ≠ 0) {a : ℝ} (ha : 0 ≤ a) (b : ℝ) :
    (∫ t : ℝ in a..b, divisorEulerMoment P (-t) - 1) ≤ normalizer P := by
  have hsum (t : ℝ) : divisorEulerMoment P (-t) - 1 =
      ∑ d ∈ P.divisors.erase 1, (d : ℝ) ^ (-t) / d.totient := by
    rw [divisorEulerMoment,
      ← Finset.sum_erase_add _ _ (Nat.one_mem_divisors.mpr hP)]
    simp
  simp_rw [hsum]
  rw [intervalIntegral.integral_finsetSum]
  · unfold normalizer
    apply Finset.sum_le_sum
    intro d hd
    have hd1 : (1 : ℝ) < d := by
      exact_mod_cast one_lt_of_mem_divisors_erase_one hd
    have hlog : 0 < Real.log d := Real.log_pos hd1
    simp_rw [Real.rpow_def_of_pos (zero_lt_one.trans hd1), mul_neg,
      ← neg_mul]
    rw [intervalIntegral.integral_div]
    calc
      (∫ t : ℝ in a..b, Real.exp (-Real.log d * t)) / (d.totient : ℝ) ≤
          (1 / Real.log d) / (d.totient : ℝ) :=
        div_le_div_of_nonneg_right (integral_exp_decay_le hlog ha b) (Nat.cast_nonneg _)
      _ = 1 / ((d.totient : ℝ) * Real.log d) := by ring
  · intro d hd
    have hdpos : 0 < (d : ℝ) :=
      Nat.cast_pos.mpr (Nat.pos_of_mem_divisors (Finset.mem_of_mem_erase hd))
    apply Continuous.intervalIntegrable
    simp_rw [Real.rpow_def_of_pos hdpos]
    fun_prop
end LongGapsBetweenPrimes
