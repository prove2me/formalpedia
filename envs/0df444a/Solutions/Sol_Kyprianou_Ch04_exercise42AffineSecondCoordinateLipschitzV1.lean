-- Prove2me | solution 1 for Kyprianou.Ch04.exercise42AffineSecondCoordinateLipschitzV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T18:27:47.509768+00:00
-- url     : https://prove2.me/submissions/c0eff593-e7b5-4a73-bba4-5c3b658c2b21

import Mathlib.Analysis.Normed.Group.Real
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Topology.MetricSpace.Lipschitz

open MeasureTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- An affine scalar path has Lipschitz constant equal to the norm of its drift. -/
theorem solution (a c : ℝ) :
    LipschitzWith ‖c‖₊ (fun t : ℝ => a + c * t) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [Real.dist_eq, coe_nnnorm, Real.norm_eq_abs]
  have h : a + c * x - (a + c * y) = c * (x - y) := by ring
  rw [h, abs_mul]
