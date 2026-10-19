-- Prove2me | solution 2 for OAI.GaussianPropeller.Reduction.gaussian_hyperplane_null
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T07:41:06.351193+00:00
-- url     : https://prove2.me/submissions/69115b9d-2802-4f6e-95cc-73e42235b38b

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianPropeller/Dual.lean:L503-L524
-- (upload_full_project.md Phase 4): solution for node OAI.GaussianPropeller.Reduction.gaussian_hyperplane_null. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_GaussianPropeller
import Definitions.Def_OAI_Probability_GaussianPropeller_Moments
import Definitions.Def_OAI_Probability_GaussianPropeller_Dual

-- ---- from OAI.Probability.GaussianPropeller.Dual ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace GaussianPropeller
open scoped RealInnerProductSpace

namespace Reduction

variable {d k : ℕ} [NeZero k]

omit [NeZero k] in

theorem gaussian_hyperplane_null (z : Space d) (hz : z ≠ 0) (c : ℝ) :
    gaussian d {x | ⟪z, x⟫ = c} = 0 := by
  let L : StrongDual ℝ (Space d) := innerSL ℝ z
  have hL : L ≠ 0 := by
    intro heq
    have hx : ⟪z, z⟫ = 0 := by
      have h := DFunLike.congr_fun heq z
      simpa [L] using h
    exact hz (inner_self_eq_zero.mp hx)
  have hv : (variance L (stdGaussian (Space d))).toNNReal ≠ 0 := by
    rw [variance_dual_stdGaussian]
    exact ne_of_gt (Real.toNNReal_pos.mpr (sq_pos_of_pos (norm_pos_iff.mpr hL)))
  have instN : NullSingletonClass
      (gaussianReal (∫ x, L x ∂stdGaussian (Space d))
        (variance L (stdGaussian (Space d))).toNNReal) := nullSingletonClass_gaussianReal hv
  have h := congrArg (fun μ : Measure ℝ => μ {c}) (IsGaussian.map_eq_gaussianReal
    (μ := stdGaussian (Space d)) L)
  rw [Measure.map_apply L.continuous.measurable (measurableSet_singleton c),
    measure_singleton] at h
  exact h

end Reduction

end GaussianPropeller

end OAI

-- ---- platform node ----
open OAI OAI.GaussianPropeller OAI.GaussianPropeller.Reduction
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace


theorem solution : type_of% @_root_.OAI.GaussianPropeller.Reduction.gaussian_hyperplane_null := @_root_.OAI.GaussianPropeller.Reduction.gaussian_hyperplane_null
