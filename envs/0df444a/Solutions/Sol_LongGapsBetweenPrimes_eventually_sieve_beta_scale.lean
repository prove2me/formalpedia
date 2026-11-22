-- Prove2me | solution 1 for LongGapsBetweenPrimes.eventually_sieve_beta_scale
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:11:38.987801+00:00
-- url     : https://prove2.me/submissions/270b73a3-71d5-4479-beb3-4b97a9571c16

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution : ∀ᶠ x : ℝ in Filter.atTop,
    48 * Real.log x ≤ x * sieveBeta x := by
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 3] with x hx hlog
  have hpow : (48 : ℝ) ≤ (Real.log x) ^ 4 := by
    calc
      (48 : ℝ) ≤ 3 ^ 4 := by norm_num
      _ ≤ (Real.log x) ^ 4 := pow_le_pow_left₀ (by norm_num) hlog 4
  calc
    48 * Real.log x ≤ (Real.log x) ^ 4 * Real.log x :=
      mul_le_mul_of_nonneg_right hpow (by linarith)
    _ = x * sieveBeta x := by
      unfold sieveBeta sieveUpperLog
      field_simp
end LongGapsBetweenPrimes
