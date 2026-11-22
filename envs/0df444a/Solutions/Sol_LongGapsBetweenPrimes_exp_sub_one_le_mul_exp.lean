-- Prove2me | solution 1 for LongGapsBetweenPrimes.exp_sub_one_le_mul_exp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:49:01.255453+00:00
-- url     : https://prove2.me/submissions/247606ce-f3f1-4ffa-bfba-163db155c3a9

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution (x : ℝ) : Real.exp x - 1 ≤ x * Real.exp x := by
  have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-x)) (Real.exp_nonneg x)
  rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h
  linarith
end LongGapsBetweenPrimes
