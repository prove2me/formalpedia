-- Prove2me | solution 1 for OAI.ArnoldCounterexample.CriticalBound.integral_fderiv_mul_skew_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T09:50:13.456984+00:00
-- url     : https://prove2.me/submissions/c62c752e-028d-4e0a-9ec9-358ea8f3bce8

-- Generated from openai/math@1581d4c lean/OAI/Geometry/Arnold/Haar.lean:L129-L150
-- (upload_full_project.md Phase 4): solution for node OAI.ArnoldCounterexample.CriticalBound.integral_fderiv_mul_skew_eq_zero. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ArnoldCounterexample
import Definitions.Def_OAI_Geometry_Arnold_Involution
import Definitions.Def_OAI_Geometry_Arnold_Projective
import Definitions.Def_OAI_Geometry_Arnold_Rotation
import Definitions.Def_OAI_Geometry_Arnold_Tangent
import Definitions.Def_OAI_Geometry_Arnold_Haar
import Theorems.Thm_OAI_ArnoldCounterexample_CriticalBound_hasDerivAt_integral_of_compact

-- ---- from OAI.Geometry.Arnold.Haar ----
namespace OAI

universe uG

noncomputable section
open scoped BigOperators ContDiff
open MeasureTheory Set Filter

open scoped BigOperators
open MeasureTheory Set Filter

namespace ArnoldCounterexample.CriticalBound

/-- The integral of a smooth infinitesimal right-translation is zero. Unlike
a manifold Stokes interface, this is proved directly from Haar invariance and
differentiation under a finite integral. -/
theorem integral_derivative_right_translate_eq_zero
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [IsFiniteMeasure μ] [μ.IsMulRightInvariant]
    (c : ℝ → G) (hc : Continuous c) (f : G → ℝ) (hf : Continuous f)
    (D : ℝ → G → ℝ) (hD : Continuous (Function.uncurry D))
    (hd : ∀ t g, HasDerivAt (fun s ↦ f (g * c s)) (D t g) t) (t : ℝ) :
    ∫ g, D t g ∂μ = 0 := by
  have h := hasDerivAt_integral_of_compact μ
    (F := fun s g ↦ f (g * c s)) (F' := D)
    (by fun_prop) hD hd t
  have heq : (fun s ↦ ∫ g, f (g * c s) ∂μ) = fun _ : ℝ ↦ ∫ g, f g ∂μ := by
    funext s
    exact integral_mul_right_eq_self f (c s)
  rw [heq] at h
  exact h.unique (hasDerivAt_const t _)

end ArnoldCounterexample.CriticalBound

namespace ArnoldCounterexample.CriticalBound

end ArnoldCounterexample.CriticalBound

open scoped Matrix.Norms.Operator ContDiff

namespace ArnoldCounterexample.CriticalBound

attribute [local instance] OAI.ArnoldCounterexample.CriticalBound.instContinuousStarRM
lemma expCurve_continuous (X : RM) (hX : star X = -X) : Continuous (expCurve X hX) := by
  exact (differentiable_exp_smul_const ℝ X).continuous.subtype_mk _

lemma right_expCurve_hasDerivAt (X : RM) (hX : star X = -X) (A : O5) (t : ℝ) :
    HasDerivAt (fun s ↦ ((A * expCurve X hX s : O5) : RM))
      (((A * expCurve X hX t : O5) : RM) * X) t := by
  convert! (hasDerivAt_exp_smul_const X t).const_mul (A : RM) using 1
  exact mul_assoc _ _ _

/-- Integration kills every left-invariant directional derivative of a C1
ambient function on this compact orthogonal group. -/
theorem integral_fderiv_mul_skew_eq_zero (f : RM → ℝ) (hf : ContDiff ℝ ∞ f)
    (X : RM) (hX : star X = -X) :
    ∫ A : O5, fderiv ℝ f (A : RM) ((A : RM) * X) ∂haar = 0 := by
  let D : ℝ → O5 → ℝ := fun t A ↦
    fderiv ℝ f ((A * expCurve X hX t : O5) : RM)
      (((A * expCurve X hX t : O5) : RM) * X)
  have hparam : Continuous (fun p : ℝ × O5 ↦ ((p.2 * expCurve X hX p.1 : O5) : RM)) := by
    exact continuous_subtype_val.comp
      (continuous_snd.mul ((expCurve_continuous X hX).comp continuous_fst))
  have hD : Continuous (Function.uncurry D) := by
    exact (hf.continuous_fderiv (by simp)).comp hparam |>.clm_apply
      (hparam.mul continuous_const)
  have hd (t : ℝ) (A : O5) : HasDerivAt (fun s ↦ f ((A * expCurve X hX s : O5) : RM))
      (D t A) t := by
    exact ((hf.differentiable (by simp) _).hasFDerivAt).comp_hasDerivAt t
      (right_expCurve_hasDerivAt X hX A t)
  have h := integral_derivative_right_translate_eq_zero haar
    (expCurve X hX) (expCurve_continuous X hX) (fun A : O5 ↦ f (A : RM))
    (hf.continuous.comp continuous_subtype_val) D hD hd 0
  simpa [D, expCurve] using h

end ArnoldCounterexample.CriticalBound

end

end OAI

-- ---- platform node ----
open OAI OAI.ArnoldCounterexample OAI.ArnoldCounterexample.CriticalBound
open scoped BigOperators ContDiff
open MeasureTheory Set Filter
open scoped BigOperators
open MeasureTheory Set Filter
open scoped Matrix.Norms.Operator ContDiff
attribute [local instance] OAI.ArnoldCounterexample.CriticalBound.instContinuousStarRM


theorem solution : type_of% @_root_.OAI.ArnoldCounterexample.CriticalBound.integral_fderiv_mul_skew_eq_zero := @_root_.OAI.ArnoldCounterexample.CriticalBound.integral_fderiv_mul_skew_eq_zero
