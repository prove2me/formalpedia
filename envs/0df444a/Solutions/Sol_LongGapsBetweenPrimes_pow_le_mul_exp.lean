-- Prove2me | solution 1 for LongGapsBetweenPrimes.pow_le_mul_exp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:49:42.709844+00:00
-- url     : https://prove2.me/submissions/e6f2f67c-0e52-4efc-98a1-aa94d6a65fd4

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {A B t : ℝ} (hA : 1 ≤ A) (hB : 0 ≤ B)
    (ht : 0 ≤ t) (hBA : B ≤ A + t) (k : ℕ) :
    B ^ k ≤ A ^ k * Real.exp ((k : ℝ) * t) := by
  have hbase : B ≤ A * Real.exp t := by
    have he := Real.add_one_le_exp t
    nlinarith [mul_nonneg (sub_nonneg.mpr hA) ht,
      mul_le_mul_of_nonneg_left he (by linarith : 0 ≤ A)]
  calc
    B ^ k ≤ (A * Real.exp t) ^ k := pow_le_pow_left₀ hB hbase k
    _ = A ^ k * Real.exp ((k : ℝ) * t) := by rw [mul_pow, Real.exp_nat_mul]
end LongGapsBetweenPrimes
