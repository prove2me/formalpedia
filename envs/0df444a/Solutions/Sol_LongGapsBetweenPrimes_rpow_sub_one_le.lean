-- Prove2me | solution 1 for LongGapsBetweenPrimes.rpow_sub_one_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:50:31.01816+00:00
-- url     : https://prove2.me/submissions/833e73ab-c28a-4fa5-adfe-23e44a016553

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_exp_sub_one_le_mul_exp

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {v γ : ℝ} (hv : 0 < v) :
    v ^ γ - 1 ≤ γ * v ^ γ * Real.log v := by
  rw [Real.rpow_def_of_pos hv]
  nlinarith [exp_sub_one_le_mul_exp (Real.log v * γ)]
end LongGapsBetweenPrimes
