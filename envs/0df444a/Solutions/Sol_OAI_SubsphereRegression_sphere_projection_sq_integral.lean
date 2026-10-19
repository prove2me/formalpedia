-- Prove2me | solution 1 for OAI.SubsphereRegression.sphere_projection_sq_integral
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T08:05:28.560512+00:00
-- url     : https://prove2.me/submissions/6223a1c0-596d-4618-9641-f47841544ad0

-- Generated from openai/math@1581d4c lean/OAI/Probability/Subsphere/Regression/Spheres.lean:L305-L321
-- (upload_full_project.md Phase 4): solution for node OAI.SubsphereRegression.sphere_projection_sq_integral. The node keeps its source
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

lemma sphere_inner_sq_eq [Nontrivial E] {v w : E} (h : ‖v‖ = ‖w‖) :
    (∫ x, ⟪v,x⟫^2 ∂ambientSphereLaw) = ∫ x, ⟪w,x⟫^2 ∂ambientSphereLaw := by
  let e := (ℝ ∙ (v-w))ᗮ.reflection
  have he : e v = w := Submodule.reflection_sub h
  have hi := (ambientSphereLaw_isometry e).integral_comp
    e.toMeasurableEquiv.measurableEmbedding (fun x => ⟪w,x⟫^2)
  rw [← he] at hi
  simp only [e.inner_map_map] at hi
  simpa only [he] using hi

lemma sphere_inner_sq_unit [Nontrivial E] {v : E} (hv : ‖v‖ = 1) :
    (∫ x, ⟪v,x⟫^2 ∂ambientSphereLaw) = 1 / (Module.finrank ℝ E : ℝ) := by
  let b := stdOrthonormalBasis ℝ E
  have hsum : ∀ x : E, (∑ i, ⟪b i,x⟫^2) = ‖x‖^2 := by
    intro x
    simpa only [real_inner_comm x, pow_two, real_inner_self_eq_norm_sq] using
      b.sum_inner_mul_inner x x
  have h : (Module.finrank ℝ E : ℝ) * (∫ x, ⟪v,x⟫^2 ∂ambientSphereLaw) = 1 := by
    calc
      _ = ∑ i : Fin (Module.finrank ℝ E), ∫ x, ⟪b i,x⟫^2 ∂ambientSphereLaw := by
        have heq : ∀ i, (∫ x, ⟪b i,x⟫^2 ∂ambientSphereLaw) =
            ∫ x, ⟪v,x⟫^2 ∂ambientSphereLaw := fun i =>
          sphere_inner_sq_eq (by rw [b.norm_eq_one, hv])
        simp only [heq, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ = ∫ x, ∑ i, ⟪b i,x⟫^2 ∂ambientSphereLaw :=
        (integral_finsetSum _ (fun i _ => sphere_inner_sq_integrable (b i))).symm
      _ = ∫ _ : E, (1 : ℝ) ∂ambientSphereLaw := by
        apply integral_congr_ae
        filter_upwards [ambientSphereLaw_ae_norm (E := E)] with x hx
        rw [hsum, hx, one_pow]
      _ = 1 := by simp
  have hd : (Module.finrank ℝ E : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℝ) (M := E)).ne'
  exact (eq_div_iff hd).2 (by simpa only [mul_comm] using h)

lemma sphere_projection_sq_integral [Nontrivial E] (U : Submodule ℝ E) :
    (∫ x, ‖U.orthogonalProjectionOnto x‖^2 ∂ambientSphereLaw) =
      (Module.finrank ℝ U : ℝ) / (Module.finrank ℝ E : ℝ) := by
  let b := stdOrthonormalBasis ℝ U
  have hsum : ∀ x : E, (∑ i, ⟪(b i : E),x⟫^2) = ‖U.orthogonalProjectionOnto x‖^2 := by
    intro x
    have h := b.sum_inner_mul_inner (U.orthogonalProjectionOnto x) (U.orthogonalProjectionOnto x)
    rw [real_inner_self_eq_norm_sq] at h
    have hi : ∀ i, ⟪U.orthogonalProjectionOnto x, b i⟫ = ⟪b i, U.orthogonalProjectionOnto x⟫ :=
      fun i => real_inner_comm _ _
    simpa only [hi, U.inner_orthogonalProjectionOnto_eq_of_mem_left, pow_two] using h
  simp_rw [← hsum]
  rw [integral_finsetSum _ (fun i _ => sphere_inner_sq_integrable (b i : E))]
  have hi : ∀ i, (∫ x, ⟪(b i : E), x⟫^2 ∂ambientSphereLaw) =
      1 / (Module.finrank ℝ E : ℝ) := fun i =>
    sphere_inner_sq_unit (by exact b.norm_eq_one i)
  simp only [hi, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one_div]

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


theorem solution : type_of% @_root_.OAI.SubsphereRegression.sphere_projection_sq_integral := @_root_.OAI.SubsphereRegression.sphere_projection_sq_integral
