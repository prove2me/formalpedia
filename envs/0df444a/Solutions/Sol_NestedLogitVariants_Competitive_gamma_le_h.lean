-- Prove2me | solution 1 for NestedLogitVariants.Competitive.gamma_le_h
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T21:59:14.300985+00:00
-- url     : https://prove2.me/submissions/20814e59-3e03-4b02-859f-3fcedd6b45f0

import Mathlib
import Definitions.Def_NestedLogitVariants_Competitive_Model

open NestedLogitVariants.Competitive in
theorem solution (γ α : ℝ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hα0 : 0 < α) (hα1 : α < 1) :
    γ ≤ (1 - α ^ γ) / (1 - α) := by
  have h := Real.geom_mean_le_arith_mean2_weighted (w₁ := γ) (w₂ := 1 - γ) (p₁ := α) (p₂ := 1)
    hγ0.le (by linarith) hα0.le zero_le_one (by ring)
  rw [Real.one_rpow, mul_one] at h
  rw [le_div_iff₀ (by linarith)]
  nlinarith
