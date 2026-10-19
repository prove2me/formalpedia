-- Prove2me | solution 1 for OAI.SubsphereCurrent.Mixture.haar_eval_integral
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T09:32:35.847445+00:00
-- url     : https://prove2.me/submissions/34a67031-ff71-4bcb-8272-1afc9f1db4f0

-- Generated from openai/math@1581d4c lean/OAI/Probability/Subsphere/Mixture/Haar.lean:L57-L73
-- (upload_full_project.md Phase 4): solution for node OAI.SubsphereCurrent.Mixture.haar_eval_integral. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SubsphereCurrent
import Definitions.Def_OAI_Probability_Subsphere_Models
import Definitions.Def_OAI_Probability_Subsphere_Regression_Geometry
import Definitions.Def_OAI_Probability_Subsphere_Regression_Gram
import Definitions.Def_OAI_Probability_Subsphere_Regression_Gaussian
import Definitions.Def_OAI_Probability_Subsphere_Regression_Projection
import Definitions.Def_OAI_Probability_Subsphere_Regression_Model
import Definitions.Def_OAI_Probability_Subsphere_Regression_Spheres
import Definitions.Def_OAI_Probability_Subsphere_Regression_Blocks
import Definitions.Def_OAI_Probability_Subsphere_Regression_Streaming
import Definitions.Def_OAI_Probability_Subsphere_Kernels_Precision
import Definitions.Def_OAI_Probability_Subsphere_Geometry_Integration
import Definitions.Def_OAI_Probability_Subsphere_Geometry_MassBounds
import Definitions.Def_OAI_Probability_Subsphere_Geometry_Affine
import Definitions.Def_OAI_Probability_Subsphere_Estimates_FixedPrecision
import Definitions.Def_OAI_Probability_Subsphere_Mixture_Haar
import Theorems.Thm_OAI_SubsphereRegression_ambientSphereLaw_isometry

-- ---- from OAI.Probability.Subsphere.Regression.Spheres ----
namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe u
namespace SubsphereRegression
open scoped Topology
open InnerProductSpace
section SphereBounds
open scoped Pointwise
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end SphereBounds

open scoped Pointwise
section MoreSphere
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma ambientSphereLaw_support : (ambientSphereLaw (E := E)).support ⊆ Metric.sphere 0 1 := by
  apply Measure.support_subset_of_isClosed Metric.isClosed_sphere
  rw [mem_ae_iff, ambientSphereLaw, Measure.map_apply (by fun_prop)
    Metric.isClosed_sphere.measurableSet.compl]
  have h : (Subtype.val : Metric.sphere (0 : E) 1 → E) ⁻¹' (Metric.sphere 0 1)ᶜ = ∅ := by
    ext x
    simp
  rw [h, measure_empty]

lemma ambientSphereLaw_ae_norm [Nontrivial E] :
    ∀ᵐ x : E ∂ambientSphereLaw, ‖x‖ = 1 := by
  filter_upwards [Measure.support_mem_ae (μ := ambientSphereLaw (E := E))] with x hx
  exact mem_sphere_zero_iff_norm.mp (ambientSphereLaw_support hx)

end MoreSphere

section FubiniAux
variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
  {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]
end FubiniAux

end SubsphereRegression
end
end

end OAI

-- ---- from OAI.Probability.Subsphere.Mixture.Haar ----
namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Mixture
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma act_mul (u v : Orthogonal E) (x : E) : act (u*v) x = act u (act v x) := rfl

lemma exists_act {x y : E} (h : ‖x‖ = ‖y‖) : ∃ u : Orthogonal E, act u x = y := by
  let e := (ℝ ∙ (x-y))ᗮ.reflection
  refine ⟨Unitary.linearIsometryEquiv.symm e,?_⟩
  change Unitary.linearIsometryEquiv (Unitary.linearIsometryEquiv.symm e) x = y
  rw [MulEquiv.apply_symm_apply]
  exact Submodule.reflection_sub h

variable [MeasurableSpace E] [BorelSpace E]

lemma haar_integral_independent {x y : E} (h : ‖x‖ = ‖y‖)
    {f : E → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ u, f (act u x) ∂orthogonalLaw) = ∫⁻ u, f (act u y) ∂orthogonalLaw := by
  obtain ⟨v,hv⟩ := exists_act h
  have hr := measurePreserving_mul_right (orthogonalLaw (E := E)) v
  have hf' : Measurable (fun u : Orthogonal E => f (act u x)) :=
    hf.comp (continuous_act.comp (continuous_id.prodMk continuous_const)).measurable
  simpa only [Function.comp_def,act_mul,hv] using (hr.lintegral_comp hf').symm

lemma haar_eval_integral [Nontrivial E] {x : E} (hx : ‖x‖ = 1)
    {f : E → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ u, f (act u x) ∂orthogonalLaw) = ∫⁻ y, f y ∂SubsphereRegression.ambientSphereLaw := by
  have hm : Measurable (fun z : E × Orthogonal E => f (act z.2 z.1)) :=
    hf.comp (continuous_act.comp continuous_swap).measurable
  have he : (∫⁻ y, ∫⁻ u, f (act u y) ∂orthogonalLaw ∂SubsphereRegression.ambientSphereLaw) =
      ∫⁻ _ : E, (∫⁻ u, f (act u x) ∂orthogonalLaw) ∂SubsphereRegression.ambientSphereLaw := by
    apply lintegral_congr_ae
    filter_upwards [SubsphereRegression.ambientSphereLaw_ae_norm] with y hy
    exact haar_integral_independent (hy.trans hx.symm) hf
  have hrot (u : Orthogonal E) :
      (∫⁻ y, f (act u y) ∂SubsphereRegression.ambientSphereLaw) =
      ∫⁻ y, f y ∂SubsphereRegression.ambientSphereLaw :=
    (SubsphereRegression.ambientSphereLaw_isometry (Unitary.linearIsometryEquiv u)).lintegral_comp hf
  rw [lintegral_lintegral_swap hm.aemeasurable] at he
  simp_rw [hrot] at he
  simpa using he.symm

end SubsphereCurrent.Mixture
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Mixture
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

end SubsphereCurrent.Mixture
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Mixture
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

end SubsphereCurrent.Mixture
end
end
section
noncomputable section
universe u v w
namespace SubsphereCurrent

end SubsphereCurrent
end
end

end OAI

-- ---- platform node ----
open OAI OAI.SubsphereCurrent OAI.SubsphereCurrent.Mixture
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace


theorem solution : type_of% @_root_.OAI.SubsphereCurrent.Mixture.haar_eval_integral := @_root_.OAI.SubsphereCurrent.Mixture.haar_eval_integral
