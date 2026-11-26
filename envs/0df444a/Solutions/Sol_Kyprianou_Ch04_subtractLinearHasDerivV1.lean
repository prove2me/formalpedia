-- Prove2me | solution 1 for Kyprianou.Ch04.subtractLinearHasDerivV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T00:42:55.987291+00:00
-- url     : https://prove2.me/submissions/7b7ca7db-5aac-469b-9790-75ecb7d54b52

import Mathlib
open Set
set_option autoImplicit false

/-- Derivative of a function after removal of its tangent slope. -/
theorem solution (f : ℝ → ℝ) (x u : ℝ) (hf : Differentiable ℝ f) :
    HasDerivAt (fun v => f v - v * deriv f x) (deriv f u - deriv f x) u := by
  have hlin : HasDerivAt (fun v : ℝ => v * deriv f x) (deriv f x) u := by
    simpa using (hasDerivAt_id u).mul_const (deriv f x)
  exact (hf u).hasDerivAt.fun_sub hlin
