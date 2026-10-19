-- Prove2me | solution 1 for OAI.SubsphereCurrent.Mixture.latitudeLaw_beta_one
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T09:53:33.509458+00:00
-- url     : https://prove2.me/submissions/4831203e-5e46-481a-bcfb-23acb5bb7afd

-- Generated from openai/math@1581d4c lean/OAI/Probability/Subsphere/Mixture/Latitude.lean:L315-L339
-- (upload_full_project.md Phase 4): solution for node OAI.SubsphereCurrent.Mixture.latitudeLaw_beta_one. The node keeps its source
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
import Definitions.Def_OAI_Probability_Subsphere_Mixture_BetaTheory
import Definitions.Def_OAI_Probability_Subsphere_Mixture_Latitude

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

lemma act_norm (u : Orthogonal E) (x : E) : ‖act u x‖ = ‖x‖ := Unitary.norm_map u x

variable [MeasurableSpace E] [BorelSpace E]

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

-- ---- from OAI.Probability.Subsphere.Mixture.BetaTheory ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

section
open MeasureTheory Set
open scoped RealInnerProductSpace
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

lemma measurable_perpCoordinate (V : Submodule ℝ E) : Measurable (perpCoordinate V) := by
  unfold perpCoordinate
  fun_prop

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

omit [MeasurableSpace E] [BorelSpace E] in
lemma perpCoordinate_blockIso (V : Submodule ℝ E) (u : Orthogonal V) (w : Orthogonal Vᗮ) (x : E) :
    perpCoordinate V (blockIso V u w x) = perpCoordinate V x := by
  rw [perpCoordinate,blockIso_apply,map_add,
    Vᗮ.orthogonalProjectionOnto_apply_of_mem_orthogonal (by simp)]
  simp [perpCoordinate,act_norm]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma latitude_e_norm (V : Submodule ℝ E) (e : Metric.sphere (0 : V) 1) : ‖(e.val : E)‖ = 1 :=
  mem_sphere_zero_iff_norm.mp e.prop

omit [MeasurableSpace E] [BorelSpace E] in
lemma latitude_rank (V : Submodule ℝ E) (e : Metric.sphere (0 : V) 1) :
    Module.finrank ℝ (latitudeSpace V e)+1 = Module.finrank ℝ E := by
  have he : (e.val : E) ≠ 0 := by intro h; have := latitude_e_norm V e; simp [h] at this
  have h := (ℝ ∙ (e.val : E)).finrank_add_finrank_orthogonal
  rw [finrank_span_singleton he] at h
  change Module.finrank ℝ (ℝ ∙ (e.val : E))ᗮ + 1 = Module.finrank ℝ E
  exact (Nat.add_comm _ _).trans h

end SubsphereCurrent.Mixture
end
end
section
open MeasureTheory
noncomputable section
namespace SubsphereCurrent.Mixture

end SubsphereCurrent.Mixture
end
end
section
open MeasureTheory ProbabilityTheory Set Module
open scoped ENNReal NNReal
noncomputable section
namespace SubsphereCurrent.Mixture

end SubsphereCurrent.Mixture
end
end
section
/-! Exact beta/gamma independence and products, needed to identify the scalar
coordinate laws in the geometric comparison. -/
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
noncomputable section
namespace SubsphereCurrent.Mixture

lemma betaPDF_measurable (a b : ℝ) : Measurable (betaPDF a b) :=
  (measurable_betaPDFReal a b).ennreal_ofReal

lemma betaMeasure_restrict_density (a b : ℝ) :
    betaMeasure a b = (volume.restrict (Ioo (0 : ℝ) 1)).withDensity (betaPDF a b) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [betaMeasure,lintegral_withDensity_eq_lintegral_mul _ (betaPDF_measurable _ _) hf,
    lintegral_withDensity_eq_lintegral_mul _ (betaPDF_measurable _ _) hf,
    ← lintegral_indicator measurableSet_Ioo]
  apply lintegral_congr
  intro x
  by_cases h : 0 < x ∧ x < 1
  · simp [h]
  · simp [Set.indicator,betaPDF,betaPDFReal,h]

end SubsphereCurrent.Mixture
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
noncomputable section
namespace SubsphereCurrent.Mixture

end SubsphereCurrent.Mixture
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Mixture
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

end SubsphereCurrent.Mixture
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Mixture
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

end SubsphereCurrent.Mixture
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Mixture
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

end SubsphereCurrent.Mixture
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Mixture
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

end SubsphereCurrent.Mixture
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
noncomputable section
namespace SubsphereCurrent.Mixture

lemma beta_ae_mem (a b : ℝ) : ∀ᵐ x ∂betaMeasure a b, x ∈ Ioo (0 : ℝ) 1 := by
  rw [betaMeasure_restrict_density]
  exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Ioo)

end SubsphereCurrent.Mixture
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Mixture
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

end SubsphereCurrent.Mixture
end
end
section
/-! Actual squared-projection beta law of the normalized Haar sphere. -/
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Mixture
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

end SubsphereCurrent.Mixture
end
end

end OAI

-- ---- from OAI.Probability.Subsphere.Mixture.Latitude ----
namespace OAI

noncomputable section

namespace SubsphereCurrent.Mixture
section
open MeasureTheory ProbabilityTheory Set

section
open scoped ENNReal NNReal RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
lemma latitude_coordinate (V : Submodule ℝ E) (e : Metric.sphere (0 : V) 1)
    (u : Orthogonal V) (x : latitudeSpace V e) {q : ℝ} (hq : 0 ≤ q) :
    perpCoordinate V (blockIso V u 1
      (Real.sqrt (1-q) • (e.val : E)+Real.sqrt q • (x : E))) =
      q * perpCoordinate V (x : E) := by
  rw [perpCoordinate_blockIso,perpCoordinate,map_add,map_smul,map_smul,
    Vᗮ.orthogonalProjectionOnto_apply_of_mem_orthogonal (by simp)]
  simp only [smul_zero,zero_add,norm_smul,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),mul_pow,Real.sq_sqrt hq,perpCoordinate]

omit [MeasurableSpace E] [BorelSpace E] in
lemma latitude_rank_one (V : Submodule ℝ E) (e : Metric.sphere (0 : V) 1)
    (hV : Module.finrank ℝ V = 1) : latitudeSpace V e = Vᗮ := by
  have he : (e.val : E) ≠ 0 := by intro h; have := latitude_e_norm V e; simp [h] at this
  have hspan : ℝ ∙ (e.val : E) = V := by
    apply Submodule.eq_of_le_of_finrank_eq
    · exact Submodule.span_le.mpr (by simp)
    · rw [finrank_span_singleton he,hV]
  exact congrArg Submodule.orthogonal hspan

omit [MeasurableSpace E] [BorelSpace E] in
lemma latitude_coordinate_rank_one (V : Submodule ℝ E) (e : Metric.sphere (0 : V) 1)
    (hV : Module.finrank ℝ V = 1) (x : latitudeSpace V e) :
    perpCoordinate V (x : E) = ‖x‖^2 := by
  have hx : (x : E) ∈ Vᗮ := (latitude_rank_one V e hV) ▸ x.prop
  unfold perpCoordinate
  change ‖Vᗮ.starProjection (x : E)‖^2 = ‖(x : E)‖^2
  rw [Submodule.starProjection_eq_self_iff.mpr hx]

lemma measurable_latitudeSampler (V : Submodule ℝ E) (e : Metric.sphere (0 : V) 1) :
    Measurable (fun z : ℝ × (Orthogonal V × latitudeSpace V e) => blockIso V z.2.1 1
      (Real.sqrt (1-z.1) • (e.val : E)+Real.sqrt z.1 • (z.2.2 : E))) :=
  ((continuous_blockIso V).comp
    (((continuous_fst.comp continuous_snd).prodMk continuous_const).prodMk
      (((continuous_const.sub continuous_fst).sqrt.smul continuous_const).add
        (continuous_fst.sqrt.smul (continuous_subtype_val.comp
          (continuous_snd.comp continuous_snd)))))).measurable

end
open scoped ENNReal NNReal

end
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

lemma latitudeLaw_beta_one (V : Submodule ℝ E) (e : Metric.sphere (0 : V) 1)
    (hV : Module.finrank ℝ V = 1) (hD : 1 < Module.finrank ℝ E)
    {a delta : ℝ} (ha : 0 < a) (hd : 0 < delta) :
    MeasurePreserving (perpCoordinate V) (latitudeLaw V e a delta) (betaMeasure a delta) := by
  have hr := latitude_rank V e
  let : Nontrivial (latitudeSpace V e) := Module.nontrivial_of_finrank_pos
    (R := ℝ) (M := latitudeSpace V e) (by omega)
  let : IsProbabilityMeasure (betaMeasure a delta) := isProbabilityMeasureBeta ha hd
  let μ := (betaMeasure a delta).prod ((orthogonalLaw (E := V)).prod
    (SubsphereRegression.ambientSphereLaw (E := latitudeSpace V e)))
  have hq : ∀ᵐ z : ℝ × (Orthogonal V × latitudeSpace V e) ∂μ, z.1 ∈ Ioo (0 : ℝ) 1 :=
    measurePreserving_fst.quasiMeasurePreserving.ae (beta_ae_mem a delta)
  have hx : ∀ᵐ z : ℝ × (Orthogonal V × latitudeSpace V e) ∂μ, ‖z.2.2‖ = 1 :=
    (measurePreserving_snd.comp measurePreserving_snd).quasiMeasurePreserving.ae
      SubsphereRegression.ambientSphereLaw_ae_norm
  refine ⟨measurable_perpCoordinate V,?_⟩
  rw [latitudeLaw,Measure.map_map (measurable_perpCoordinate V) (measurable_latitudeSampler V e)]
  calc
    _ = μ.map Prod.fst := by
      apply Measure.map_congr
      filter_upwards [hq,hx] with z hz hzx
      dsimp only [Function.comp_apply]
      rw [latitude_coordinate V e z.2.1 z.2.2 hz.1.le,
        latitude_coordinate_rank_one V e hV,hzx,one_pow,mul_one]
    _ = _ := measurePreserving_fst.map_eq

end SubsphereCurrent.Mixture

end

end OAI

-- ---- platform node ----
open OAI OAI.SubsphereCurrent OAI.SubsphereCurrent.Mixture
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace


theorem solution : type_of% @_root_.OAI.SubsphereCurrent.Mixture.latitudeLaw_beta_one := @_root_.OAI.SubsphereCurrent.Mixture.latitudeLaw_beta_one
