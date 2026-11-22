-- Prove2me | solution 1 for LongGapsBetweenPrimes.integral_exp_decay_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:56:13.884422+00:00
-- url     : https://prove2.me/submissions/7d8bda4a-b486-4657-ae35-815f73cb6a2a

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {L a : ℝ} (hL : 0 < L) (ha : 0 ≤ a) (b : ℝ) :
    (∫ t : ℝ in a..b, Real.exp (-L * t)) ≤ 1 / L := by
  rw [intervalIntegral.integral_comp_mul_left Real.exp (neg_ne_zero.mpr hL.ne'),
    integral_exp, smul_eq_mul, inv_neg, neg_mul, ← mul_neg, neg_sub, ← div_eq_inv_mul]
  exact div_le_div_of_nonneg_right
    ((sub_le_self _ (Real.exp_nonneg _)).trans
      (Real.exp_le_one_iff.mpr (by nlinarith))) hL.le
end LongGapsBetweenPrimes
