-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_exponential_real_remainder
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T21:55:51.746819+00:00
-- url     : https://prove2.me/submissions/e82a8039-255f-4836-93c5-ecd02995ff53

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_kw48_exp_remainder
open MeasureTheory Filter ProbabilityTheory Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution (x : ℝ) (z : ℂ) (hx : 0 ≤ x) (hs : x*‖z‖ ≤ 1) :
    |1-(Complex.exp ((x:ℂ)*z)).re+x*z.re| ≤ (x*‖z‖)^2 := by
  let w : ℂ := (x:ℂ)*z
  have hw : ‖w‖ = x*‖z‖ := by simp [w,norm_mul,Real.norm_of_nonneg hx]
  have h := Kyprianou.Ch04.kw48_exp_remainder (-w) (by simpa [norm_neg,hw] using hs)
  rw [neg_neg,norm_neg,hw] at h
  have hre := (Complex.abs_re_le_norm (1-Complex.exp w-(-w))).trans h
  simpa [w,Complex.sub_re,Complex.mul_re,Complex.neg_re] using hre
