-- Prove2me | solution 1 for Kyprianou.Ch04.exercise42LipschitzTimeDerivativeBoundV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T20:00:43.771664+00:00
-- url     : https://prove2.me/submissions/09d144bf-e4a5-4d5a-8727-d506259a0e94

import Mathlib.Analysis.Calculus.Deriv.Basic
open Set
open scoped NNReal
set_option autoImplicit false

/-- The extended NNReal Lipschitz path has uniformly bounded real derivative. -/
theorem solution
    (U : NNReal → ℝ) (K : NNReal) (hU : LipschitzWith K U) (u : ℝ) :
    ‖deriv (fun z : ℝ => U z.toNNReal) u‖ ≤ (K : ℝ) := by
  have hL : LipschitzWith K (fun z : ℝ => U z.toNNReal) := by
    simpa only [mul_one, Function.comp_def] using
      hU.comp Real.lipschitzWith_toNNReal
  exact norm_deriv_le_of_lipschitz hL
