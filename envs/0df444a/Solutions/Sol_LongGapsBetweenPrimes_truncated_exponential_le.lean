-- Prove2me | solution 1 for LongGapsBetweenPrimes.truncated_exponential_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:10:00.510922+00:00
-- url     : https://prove2.me/submissions/8b334a00-42e9-4462-8b18-760df37fc41c

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_exp_neg_nat_mul_log

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {n : ℕ} {x β C : ℝ} (hx : 0 < x) (hβ : 0 ≤ β)
    (hsize : (n : ℝ) * C ≤ x / 16) (hlog : 48 * Real.log x ≤ x * β) :
    sieveD x ^ (-β) * Real.exp ((n : ℝ) * C * β) ≤ 1 / x ^ 3 := by
  rw [sieveD, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, ← Real.exp_add,
    ← exp_neg_nat_mul_log hx 3]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_right hsize hβ]
end LongGapsBetweenPrimes
