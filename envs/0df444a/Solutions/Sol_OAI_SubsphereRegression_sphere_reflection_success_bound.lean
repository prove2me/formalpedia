-- Prove2me | solution 1 for OAI.SubsphereRegression.sphere_reflection_success_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T08:07:04.812656+00:00
-- url     : https://prove2.me/submissions/8bf3151e-ca63-428b-be6d-b9ea214c22ae

-- Generated from openai/math@1581d4c lean/OAI/Probability/Subsphere/Regression/Spheres.lean:L380-L417
-- (upload_full_project.md Phase 4): solution for node OAI.SubsphereRegression.sphere_reflection_success_bound. The node keeps its source
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

omit [MeasurableSpace E] [BorelSpace E] in
lemma reflection_dist (U : Submodule ℝ E) (x : E) :
    dist x (U.reflection x) = 2 * ‖Uᗮ.starProjection x‖ := by
  rw [dist_eq_norm, Submodule.reflection_apply]
  have heq : x - (2 • U.starProjection x - x) = (2 : ℝ) • Uᗮ.starProjection x := by
    rw [Submodule.starProjection_orthogonal]
    simp only [sub_apply, ContinuousLinearMap.id_apply, two_smul ℝ]
    abel
  rw [heq, norm_smul]
  norm_num

lemma sphere_projection_large [Nontrivial E] (U : Submodule ℝ E)
    (hU : 4 * Module.finrank ℝ U ≤ Module.finrank ℝ E) :
    sphereLaw {x : Metric.sphere (0 : E) 1 | (4/5 : ℝ) ≤ ‖U.orthogonalProjectionOnto x.val‖^2} ≤
      ENNReal.ofReal (5/16 : ℝ) := by
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
  have hdiv : (Module.finrank ℝ U : ℝ) / (Module.finrank ℝ E : ℝ) ≤ 1/4 := by
    rw [div_le_iff₀ hd]
    have : (4 : ℝ) * Module.finrank ℝ U ≤ Module.finrank ℝ E := by exact_mod_cast hU
    linarith
  calc
    _ ≤ ENNReal.ofReal (1/4 : ℝ) / ENNReal.ofReal (4/5 : ℝ) := by gcongr
    _ = ENNReal.ofReal (5/16 : ℝ) := by
      rw [← ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4/5)]
      norm_num

lemma sphere_reflection_success_bound [Nontrivial E] (U : Submodule ℝ E)
    (hU : 4 * Module.finrank ℝ U ≤ Module.finrank ℝ E)
    (S : Set (Metric.sphere (0 : E) 1)) (hS : NullMeasurableSet S sphereLaw)
    (hsep : ∀ s ∈ S, sphereIsometry U.reflection s ∈ S →
      dist s.val (U.reflection s.val) ≤ 1/5) :
    sphereLaw S ≤ ENNReal.ofReal (21/32 : ℝ) := by
  let f := sphereIsometry U.reflection
  have hp := sphereIsometry_preserving U.reflection
  have hi : S ∩ f ⁻¹' S ⊆
      {x : Metric.sphere (0 : E) 1 | (4/5 : ℝ) ≤ ‖U.orthogonalProjectionOnto x.val‖^2} := by
    intro s hs
    have hd := hsep s hs.1 hs.2
    rw [reflection_dist] at hd
    have hn := U.norm_sq_eq_add_norm_sq_starProjection s.val
    rw [mem_sphere_zero_iff_norm.mp s.property] at hn
    change (4/5 : ℝ) ≤ ‖U.orthogonalProjectionOnto s.val‖^2
    have he : ‖U.starProjection s.val‖ = ‖U.orthogonalProjectionOnto s.val‖ := rfl
    rw [he] at hn
    nlinarith [norm_nonneg (Uᗮ.starProjection s.val)]
  have hinter := (measure_mono hi).trans (sphere_projection_large U hU)
  have heq := measure_union_add_inter₀ S (hS.preimage hp.quasiMeasurePreserving)
  rw [hp.measure_preimage hS] at heq
  calc
    sphereLaw S = ENNReal.ofReal (1/2 : ℝ) * (sphereLaw S + sphereLaw S) := by
      rw [← two_mul, ← mul_assoc]
      have hc : ENNReal.ofReal (1/2 : ℝ) * 2 = 1 := by
        rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1/2)]
        norm_num
      rw [hc, one_mul]
    _ = ENNReal.ofReal (1/2 : ℝ) *
        (sphereLaw (S ∪ f ⁻¹' S) + sphereLaw (S ∩ f ⁻¹' S)) := by rw [heq]
    _ ≤ ENNReal.ofReal (1/2 : ℝ) * (1 + ENNReal.ofReal (5/16 : ℝ)) := by
      exact mul_le_mul' le_rfl (add_le_add prob_le_one hinter)
    _ = ENNReal.ofReal (21/32 : ℝ) := by
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1)
        (by norm_num : (0 : ℝ) ≤ 5/16),
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1/2)]
      norm_num

end MoreSphere

section FubiniAux
variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
  {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]
end FubiniAux

end SubsphereRegression
end
end

end OAI

-- ---- platform node ----
open OAI OAI.SubsphereRegression
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
open scoped Topology
open InnerProductSpace
open scoped Pointwise


theorem solution : type_of% @_root_.OAI.SubsphereRegression.sphere_reflection_success_bound := @_root_.OAI.SubsphereRegression.sphere_reflection_success_bound
