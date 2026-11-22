-- Prove2me | solution 1 for LongGapsBetweenPrimes.exp_neg_nat_mul_log
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:35:01.682609+00:00
-- url     : https://prove2.me/submissions/81c31f1b-563c-4b85-a9fd-d27477f2df79

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {x : ℝ} (hx : 0 < x) (n : ℕ) :
    Real.exp (-(n : ℝ) * Real.log x) = 1 / x ^ n := by
  rw [neg_mul, Real.exp_neg, Real.exp_nat_mul, Real.exp_log hx, one_div]
end LongGapsBetweenPrimes
