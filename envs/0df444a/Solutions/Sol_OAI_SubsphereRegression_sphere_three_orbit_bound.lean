-- Prove2me | solution 1 for OAI.SubsphereRegression.sphere_three_orbit_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T09:21:04.013233+00:00
-- url     : https://prove2.me/submissions/13b6e5ea-158d-4ec4-aaed-8b7e2d57dc39

-- Generated from openai/math@1581d4c lean/OAI/Probability/Subsphere/Estimates/HalfPrecision.lean:L63-L123
-- (upload_full_project.md Phase 4): solution for node OAI.SubsphereRegression.sphere_three_orbit_bound. The node keeps its source
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
import Theorems.Thm_OAI_SubsphereCurrent_Quarter_extend_norm_sq
import Theorems.Thm_OAI_SubsphereCurrent_Quarter_extend_square_norm_sq
import Theorems.Thm_OAI_SubsphereRegression_ambientSphereLaw_isometry
import Theorems.Thm_OAI_SubsphereRegression_sphere_projection_sq_integral

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

lemma sphere_inner_sq_integrable [Nontrivial E] (v : E) :
    Integrable (fun x => ⟪v,x⟫^2) (ambientSphereLaw (E := E)) := by
  apply (integrable_const (‖v‖^2)).mono' (by fun_prop)
  filter_upwards [ambientSphereLaw_ae_norm (E := E)] with x hx
  have h := abs_real_inner_le_norm v x
  rw [hx, mul_one] at h
  simpa only [Real.norm_eq_abs, abs_pow, sq_abs] using
    (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _) |>.2 h)

lemma sphere_projection_sq_integrable [Nontrivial E] (U : Submodule ℝ E) :
    Integrable (fun x => ‖U.orthogonalProjectionOnto x‖^2) (ambientSphereLaw (E := E)) := by
  let b := stdOrthonormalBasis ℝ U
  have hsum : ∀ x : E, (∑ i, ⟪(b i : E),x⟫^2) = ‖U.orthogonalProjectionOnto x‖^2 := by
    intro x
    have h := b.sum_inner_mul_inner (U.orthogonalProjectionOnto x) (U.orthogonalProjectionOnto x)
    rw [real_inner_self_eq_norm_sq] at h
    have hi : ∀ i, ⟪U.orthogonalProjectionOnto x, b i⟫ = ⟪b i, U.orthogonalProjectionOnto x⟫ :=
      fun i => real_inner_comm _ _
    simpa only [hi, U.inner_orthogonalProjectionOnto_eq_of_mem_left, pow_two] using h
  simp_rw [← hsum]
  exact integrable_finsetSum _ (fun i _ => sphere_inner_sq_integrable (b i : E))

lemma sphereIsometry_preserving [Nontrivial E] (e : E ≃ₗᵢ[ℝ] E) :
    MeasurePreserving (sphereIsometry e) (sphereLaw (E := E)) (sphereLaw (E := E)) := by
  refine ⟨(sphereIsometry e).continuous.measurable, ?_⟩
  apply (MeasurableEmbedding.subtype_coe Metric.isClosed_sphere.measurableSet).map_injective
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  change (sphereLaw (E := E)).map (e ∘ Subtype.val) = ambientSphereLaw
  rw [← Measure.map_map e.continuous.measurable (by fun_prop)]
  exact (ambientSphereLaw_isometry e).map_eq

end MoreSphere

section FubiniAux
variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
  {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]
end FubiniAux

end SubsphereRegression
end
end

end OAI

-- ---- from OAI.Probability.Subsphere.Geometry.Integration ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Polar
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

end SubsphereCurrent.Polar
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Polar
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

end SubsphereCurrent.Polar
end
end
section
/-! Isometric naturality of the exact normalized Haar spherical law. -/
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace Pointwise
noncomputable section
namespace SubsphereCurrent.Polar
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

end SubsphereCurrent.Polar
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Slice
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end SubsphereCurrent.Slice
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Weighted

end SubsphereCurrent.Weighted
end
end
section
open MeasureTheory Set
open scoped ENNReal NNReal
noncomputable section
namespace SubsphereCurrent.Polar

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

end SubsphereCurrent.Polar
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Slice
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

end SubsphereCurrent.Slice
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Slice
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

end SubsphereCurrent.Slice
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Quarter
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma extend_apply (F : Submodule ℝ E) (e : F ≃ₗᵢ[ℝ] F) (x : E) :
    extend F e x = (e (F.orthogonalProjectionOnto x) : E) + Fᗮ.starProjection x := by
  simp [extend, Submodule.orthogonalDecomposition_symm_apply]

lemma extend_fixed (F : Submodule ℝ E) (e : F ≃ₗᵢ[ℝ] F) {x : E} (hx : x ∈ Fᗮ) :
    extend F e x = x := by
  rw [extend_apply, F.orthogonalProjectionOnto_apply_of_mem_orthogonal hx]
  simp [Submodule.starProjection_eq_self_iff.mpr hx]

end SubsphereCurrent.Quarter
end
end

end OAI

-- ---- from OAI.Probability.Subsphere.Estimates.HalfPrecision ----
namespace OAI

noncomputable section

namespace SubsphereRegression
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
lemma sphere_projection_eighth [Nontrivial E] (U : Submodule ℝ E)
    (hU : 16 * Module.finrank ℝ U ≤ Module.finrank ℝ E) :
    sphereLaw {x : Metric.sphere (0 : E) 1 | (4/5 : ℝ) ≤ ‖U.orthogonalProjectionOnto x.val‖^2} ≤
      ENNReal.ofReal (5/64 : ℝ) := by
  have hi := ofReal_integral_eq_lintegral_ofReal (sphere_projection_sq_integrable U)
    (Filter.Eventually.of_forall fun x => sq_nonneg ‖U.orthogonalProjectionOnto x‖)
  rw [sphere_projection_sq_integral] at hi
  have hmark := meas_ge_le_lintegral_div
    (μ := ambientSphereLaw (E := E)) (f := fun x => ENNReal.ofReal (‖U.orthogonalProjectionOnto x‖^2))
    (by fun_prop) (by norm_num : ENNReal.ofReal (4/5 : ℝ) ≠ 0) (ENNReal.ofReal_ne_top : ENNReal.ofReal (4/5 : ℝ) ≠ ∞)
  rw [← hi] at hmark
  have hset : {x : E | ENNReal.ofReal (4/5 : ℝ) ≤ ENNReal.ofReal (‖U.orthogonalProjectionOnto x‖^2)} =
      {x : E | (4/5 : ℝ) ≤ ‖U.orthogonalProjectionOnto x‖^2} := by
    ext x
    change ENNReal.ofReal (4/5 : ℝ) ≤ _ ↔ _
    exact ENNReal.ofReal_le_ofReal_iff (sq_nonneg _)
  rw [hset, ambientSphereLaw,
    (MeasurableEmbedding.subtype_coe Metric.isClosed_sphere.measurableSet).map_apply] at hmark
  apply hmark.trans
  have hd : (0 : ℝ) < Module.finrank ℝ E := by
    exact_mod_cast Module.finrank_pos (R := ℝ) (M := E)
  have hdiv : (Module.finrank ℝ U : ℝ) / (Module.finrank ℝ E : ℝ) ≤ 1/16 := by
    rw [div_le_iff₀ hd]
    have : (16 : ℝ) * Module.finrank ℝ U ≤ Module.finrank ℝ E := by exact_mod_cast hU
    linarith
  calc
    _ ≤ ENNReal.ofReal (1/16 : ℝ) / ENNReal.ofReal (4/5 : ℝ) := by gcongr
    _ = ENNReal.ofReal (5/64 : ℝ) := by
      rw [← ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4/5)]
      norm_num

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
lemma three_sets_bound {μ : Measure E} [IsProbabilityMeasure μ] {A B C : Set E}
    (_hA : NullMeasurableSet A μ) (hB : NullMeasurableSet B μ) (hC : NullMeasurableSet C μ)
    {b : ℝ≥0∞} (hAB : μ (A∩B) ≤ b) (hAC : μ (A∩C) ≤ b) (hBC : μ (B∩C) ≤ b) :
    μ A + μ B + μ C ≤ 1 + (b+b+b) := by
  have h₁ := measure_union_add_inter₀ A hB
  have h₂ := measure_union_add_inter₀ (A∪B) hC
  calc
    _ = (μ (A∪B) + μ C) + μ (A∩B) := by rw [← h₁]; ac_rfl
    _ = μ ((A∪B)∪C) + μ ((A∪B)∩C) + μ (A∩B) := by rw [h₂]
    _ ≤ 1 + (μ (A∩C)+μ (B∩C)) + b := by
      apply add_le_add _ hAB
      apply add_le_add prob_le_one
      rw [union_inter_distrib_right]
      exact measure_union_le _ _
    _ ≤ 1 + (b+b) + b := by gcongr
    _ = _ := by ac_rfl

lemma sphere_three_orbit_bound [Nontrivial E] (F : Submodule ℝ E)
    (hF : 16*Module.finrank ℝ Fᗮ ≤ Module.finrank ℝ E)
    (e : F ≃ₗᵢ[ℝ] F) (he : ∀ x, ⟪x,e x⟫ = 0) (he2 : ∀ x, e (e x) = -x)
    (S : Set (Metric.sphere (0 : E) 1)) (hS : NullMeasurableSet S sphereLaw)
    (hnear : ∀ x y : Metric.sphere (0 : E) 1,
      (∀ u : E, u ∈ Fᗮ → ⟪u,x.val⟫ = ⟪u,y.val⟫) → x ∈ S → y ∈ S →
      dist x.val y.val ≤ 1/5) :
    sphereLaw S ≤ ENNReal.ofReal (7/16 : ℝ) := by
  let q := SubsphereCurrent.Quarter.extend F e
  let f := sphereIsometry q
  have hp := sphereIsometry_preserving q
  have hpf := hp.comp hp
  let B := {x : Metric.sphere (0 : E) 1 | (4/5 : ℝ) ≤ ‖Fᗮ.orthogonalProjectionOnto x.val‖^2}
  have hB : sphereLaw B ≤ ENNReal.ofReal (5/64 : ℝ) := sphere_projection_eighth Fᗮ hF
  have hlabel (x : Metric.sphere (0 : E) 1) :
      ∀ u : E, u ∈ Fᗮ → ⟪u,x.val⟫ = ⟪u,(f x).val⟫ := by
    intro u hu
    have hr := q.inner_map_map u x.val
    rw [SubsphereCurrent.Quarter.extend_fixed F e hu] at hr
    exact hr.symm
  have hsmall (x : Metric.sphere (0 : E) 1) {c : ℝ}
      (hc : 2 ≤ c) (hd : dist x.val (f x).val^2 = c*‖F.orthogonalProjectionOnto x.val‖^2)
      (hne : dist x.val (f x).val ≤ 1/5) : x ∈ B := by
    have hn := F.norm_sq_eq_add_norm_sq_starProjection x.val
    rw [mem_sphere_zero_iff_norm.mp x.property] at hn
    change (4/5 : ℝ) ≤ ‖Fᗮ.orthogonalProjectionOnto x.val‖^2
    change (1 : ℝ)^2 = ‖F.orthogonalProjectionOnto x.val‖^2 +
      ‖Fᗮ.orthogonalProjectionOnto x.val‖^2 at hn
    nlinarith [(dist_nonneg : 0 ≤ dist x.val (f x).val), sq_nonneg ‖F.orthogonalProjectionOnto x.val‖,
      mul_nonneg (sub_nonneg.mpr hc) (sq_nonneg ‖F.orthogonalProjectionOnto x.val‖)]
  have hAB : S ∩ f ⁻¹' S ⊆ B := by
    intro x hx
    exact hsmall x (by norm_num) (SubsphereCurrent.Quarter.extend_norm_sq F e he x.val)
      (hnear x (f x) (hlabel x) hx.1 hx.2)
  have hAC : S ∩ (f ∘ f) ⁻¹' S ⊆ B := by
    intro x hx
    have hne := hnear x (f (f x)) (fun u hu => (hlabel x u hu).trans (hlabel (f x) u hu)) hx.1 hx.2
    have hd := SubsphereCurrent.Quarter.extend_square_norm_sq F e he2 x.val
    have hn := F.norm_sq_eq_add_norm_sq_starProjection x.val
    rw [mem_sphere_zero_iff_norm.mp x.property] at hn
    change (4/5 : ℝ) ≤ ‖Fᗮ.orthogonalProjectionOnto x.val‖^2
    change (1 : ℝ)^2 = ‖F.orthogonalProjectionOnto x.val‖^2 +
      ‖Fᗮ.orthogonalProjectionOnto x.val‖^2 at hn
    change dist x.val (f (f x)).val^2 = _ at hd
    nlinarith [(dist_nonneg : 0 ≤ dist x.val (f (f x)).val)]
  have hBC : sphereLaw (f ⁻¹' S ∩ (f ∘ f) ⁻¹' S) ≤ ENNReal.ofReal (5/64 : ℝ) := by
    have heq : f ⁻¹' S ∩ (f ∘ f) ⁻¹' S = f ⁻¹' (S ∩ f ⁻¹' S) := rfl
    rw [heq,hp.measure_preimage (hS.inter (hS.preimage hp.quasiMeasurePreserving))]
    exact (measure_mono hAB).trans hB
  have hh := three_sets_bound hS (hS.preimage hp.quasiMeasurePreserving)
    (hS.preimage hpf.quasiMeasurePreserving) ((measure_mono hAB).trans hB)
    ((measure_mono hAC).trans hB) hBC
  rw [hp.measure_preimage hS,hpf.measure_preimage hS] at hh
  have hr := ENNReal.toReal_mono (by norm_num :
    (1+(ENNReal.ofReal (5/64 : ℝ)+ENNReal.ofReal (5/64 : ℝ)+ENNReal.ofReal (5/64 : ℝ))) ≠ ∞) hh
  simp only [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
    ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _,measure_ne_top _ _⟩) (measure_ne_top _ _)] at hr
  norm_num [ENNReal.toReal_add, ENNReal.add_ne_top] at hr
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
  norm_num
  linarith

namespace Learner
end Learner
end SubsphereRegression
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
universe u
namespace SubsphereRegression
namespace Learner
end Learner

end SubsphereRegression
end
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
universe u
namespace SubsphereCurrent

end SubsphereCurrent

end

end OAI

-- ---- platform node ----
open OAI OAI.SubsphereRegression
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace


theorem solution : type_of% @_root_.OAI.SubsphereRegression.sphere_three_orbit_bound := @_root_.OAI.SubsphereRegression.sphere_three_orbit_bound
