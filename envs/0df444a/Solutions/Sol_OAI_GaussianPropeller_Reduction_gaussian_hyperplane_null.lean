-- Prove2me | solution 1 for OAI.GaussianPropeller.Reduction.gaussian_hyperplane_null
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:14:23.813958+00:00
-- url     : https://prove2.me/submissions/999b9dce-7afd-418f-9454-f0a255ddd4cb

import Mathlib
import Definitions.Def_GaussianPropeller
import Definitions.Def_OAI_Probability_GaussianPropeller_Moments
import Definitions.Def_OAI_Probability_GaussianPropeller_Dual

open OAI OAI.GaussianPropeller OAI.GaussianPropeller.Reduction
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
variable {d k : ℕ} [NeZero k]


omit [NeZero k] in
theorem solution (z : Space d) (hz : z ≠ 0) (c : ℝ) :
    gaussian d {x | ⟪z, x⟫ = c} = 0 := by
  let L : StrongDual ℝ (Space d) := innerSL ℝ z
  have hset : {x : Space d | ⟪z, x⟫ = c} = L ⁻¹' {c} := by
    ext x; simp [L]
  rw [hset, gaussian, ← Measure.map_apply L.continuous.measurable (measurableSet_singleton c),
    IsGaussian.map_eq_gaussianReal, variance_dual_stdGaussian]
  have hL : ‖L‖ = ‖z‖ := innerSL_apply_norm ℝ z
  have hv : (‖L‖ ^ 2).toNNReal ≠ 0 := by
    rw [hL]; intro h
    rw [Real.toNNReal_eq_zero] at h
    have : 0 < ‖z‖ := norm_pos_iff.mpr hz
    nlinarith
  exact gaussianReal_absolutelyContinuous _ hv (Real.volume_singleton)

