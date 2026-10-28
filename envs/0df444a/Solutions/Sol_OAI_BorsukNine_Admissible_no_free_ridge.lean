-- Prove2me | solution 1 for OAI.BorsukNine.Admissible.no_free_ridge
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T21:01:15.185991+00:00
-- url     : https://prove2.me/submissions/58be17e2-2337-475b-b58c-ab07005a6cd9

import Mathlib
import Definitions.Def_OAIQ058B000
import Theorems.Thm_OAI_BorsukNine_Admissible_localBlockMix_hit
import Theorems.Thm_OAI_BorsukNine_Admissible_localBlockMix_ne_zero
import Theorems.Thm_OAI_BorsukNine_Admissible_localBlockModel_ne_zero
import Theorems.Thm_OAI_BorsukNine_Admissible_localBlockModel_ray
import Theorems.Thm_OAI_BorsukNine_Admissible_original_ray_level
import Theorems.Thm_OAI_BorsukNine_Admissible_regularPatch_isOpen
import Theorems.Thm_OAI_BorsukNine_Admissible_regular_facet_level_even
import Theorems.Thm_OAI_BorsukNine_trace_patch_models

section
-- module Solutions.OAIQ058_BK.Compat
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_MatrixGeometry_MatrixNorm
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace ContDiff
open scoped Manifold
open MeasureTheory Set Metric
open scoped ENNReal Pointwise Matrix
section MatrixNorm
open scoped MatrixOrder Matrix.Norms.L2Operator

variable {ν : Type*} [Fintype ν] [DecidableEq ν]
local notation "E" => EuclideanSpace ℝ ν

lemma matrix_action_norm_sq (A : Matrix ν ν ℝ) (x : E) :
    ‖(Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)) A x‖ ^ 2 =
      ⟪x, (Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)) (star A * A) x⟫ := by
  rw [map_mul, map_star]
  change ‖(Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)) A x‖ ^ 2 =
    ⟪x, (star ((Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)) A)) ((Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)) A x)⟫
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,
    real_inner_self_eq_norm_sq]

lemma sqrt_action_norm_sq (Q : Matrix ν ν ℝ) (hQ : 0 ≤ Q) (x : E) :
    ‖(Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)) (CFC.sqrt Q) x‖ ^ 2 = ⟪x, (Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)) Q x⟫ := by
  rw [matrix_action_norm_sq, (CFC.sqrt_nonneg Q).star_eq, CFC.sqrt_mul_sqrt_self Q hQ]

end MatrixNorm

section MatrixRange
open scoped MatrixOrder Matrix.Norms.L2Operator

variable {ν : Type*} [Fintype ν] [DecidableEq ν]
local notation "op" => Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)
lemma matrix_sqrt_range (Q : Matrix ν ν ℝ) (hQ : 0 ≤ Q) :
    LinearMap.range (op (CFC.sqrt Q)).toLinearMap = LinearMap.range (op Q).toLinearMap := by
  have hs : star (op (CFC.sqrt Q)) = op (CFC.sqrt Q) := by
    rw [← map_star, (CFC.sqrt_nonneg Q).star_eq]
  have hh := LinearMap.range_adjoint_comp_self (op (CFC.sqrt Q)).toLinearMap
  have ha : (op (CFC.sqrt Q)).toLinearMap.adjoint = (op (CFC.sqrt Q)).toLinearMap := by
    change (ContinuousLinearMap.adjoint (op (CFC.sqrt Q))).toLinearMap = _
    rw [← ContinuousLinearMap.star_eq_adjoint, hs]
  rw [ha] at hh
  have hm : (op (CFC.sqrt Q)).toLinearMap.comp (op (CFC.sqrt Q)).toLinearMap = (op Q).toLinearMap := by
    change (op (CFC.sqrt Q) * op (CFC.sqrt Q)).toLinearMap = _
    rw [← map_mul, CFC.sqrt_mul_sqrt_self Q hQ]
  rw [hm] at hh
  exact hh.symm

end MatrixRange

end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_SphereGeometry_HomogeneousLift
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace ContDiff
open scoped Manifold
section HomogeneousLift
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {ι : Type*}

lemma homogeneousLift_unit (f : V → ι → ℝ) {v : V} (hv : ‖v‖ = 1) :
    homogeneousLift f v = f v := by
  ext i
  simp [homogeneousLift, hv]

variable [Fintype ι]

lemma Admissible.lift_nonneg {f : V → ι → ℝ} (hf : Admissible f) (v : V) (i : ι) :
    0 ≤ homogeneousLift f v i := by
  by_cases hv : v = 0
  · simp [hv]
  · exact mul_nonneg (sq_nonneg _) (hf.nonneg _ (norm_smul_inv_norm (𝕜 := ℝ) hv) i)

lemma Admissible.lift_sum {f : V → ι → ℝ} (hf : Admissible f) (v : V) :
    ∑ i, homogeneousLift f v i = ‖v‖ ^ 2 := by
  classical
  by_cases hv : v = 0
  · simp [hv]
  · simp only [homogeneousLift, ← Finset.mul_sum]
    have hn : ‖(‖v‖⁻¹ : ℝ) • v‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg v))]
      exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)
    rw [hf.sum_one _ hn, mul_one]

lemma Admissible.lift_le {f : V → ι → ℝ} (hf : Admissible f) (v : V) (i : ι) :
    homogeneousLift f v i ≤ ‖v‖ ^ 2 := by
  classical
  rw [← hf.lift_sum v]
  exact Finset.single_le_sum (fun j _ => hf.lift_nonneg v j) (Finset.mem_univ i)

lemma Admissible.lift_norm_le {f : V → ι → ℝ} (hf : Admissible f) (v : V) :
    ‖homogeneousLift f v‖ ≤ ‖v‖ ^ 2 := by
  rw [pi_norm_le_iff_of_nonneg (sq_nonneg _)]
  intro i
  simpa only [Real.norm_eq_abs, abs_of_nonneg (hf.lift_nonneg v i)] using hf.lift_le v i

omit [Fintype ι] in
lemma homogeneousLift_smul_pos (f : V → ι → ℝ) (v : V) {t : ℝ} (ht : 0 < t) :
    homogeneousLift f (t • v) = t ^ 2 • homogeneousLift f v := by
  ext i
  have he : (‖t • v‖⁻¹ : ℝ) • (t • v) = (‖v‖⁻¹ : ℝ) • v := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht, mul_inv_rev, smul_smul]
    congr 1
    field_simp
  change ‖t • v‖ ^ 2 * f ((‖t • v‖⁻¹ : ℝ) • (t • v)) i = t ^ 2 * (‖v‖ ^ 2 * f ((‖v‖⁻¹ : ℝ) • v) i)
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
  ring

lemma Admissible.lift_continuous {f : V → ι → ℝ} (hf : Admissible f) :
    Continuous (homogeneousLift f) := by
  apply continuous_iff_continuousAt.mpr
  intro v
  by_cases hv : v = 0
  · subst v
    rw [ContinuousAt, homogeneousLift_zero]
    apply squeeze_zero_norm (fun x => hf.lift_norm_le x)
    have hc : Continuous (fun x : V => ‖x‖ ^ 2) := continuous_norm.pow 2
    simpa using hc.tendsto (0 : V)
  · have hn : ContinuousAt (fun x : V => (‖x‖⁻¹ : ℝ) • x) v :=
      (continuous_norm.continuousAt.inv₀ (norm_ne_zero_iff.mpr hv)).smul continuousAt_id
    apply continuousAt_pi.mpr
    intro i
    exact (continuous_norm.continuousAt.pow 2).mul ((hf.smooth i).continuous.continuousAt.comp hn)

end HomogeneousLift

open MeasureTheory Set Metric
open scoped ENNReal Pointwise Matrix

end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_SphereGeometry_SphereMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace ContDiff
open scoped Manifold
open MeasureTheory Set Metric
open scoped ENNReal Pointwise Matrix
section SphereMeasure
variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V]

variable {V}

omit [Nontrivial V] in
lemma sphereRotation_preserves_toSphere (e : V ≃ₗᵢ[ℝ] V) :
    MeasurePreserving (sphereRotation e) volume.toSphere volume.toSphere := by
  refine ⟨(sphereRotation e).measurable, ?_⟩
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (sphereRotation e).measurable hs,
    Measure.toSphere_apply' _ ((sphereRotation e).measurable hs), Measure.toSphere_apply' _ hs]
  congr 1
  have hset : Ioo (0 : ℝ) 1 • (Subtype.val '' (sphereRotation e ⁻¹' s)) =
      e ⁻¹' (Ioo (0 : ℝ) 1 • (Subtype.val '' s)) := by
    ext x
    constructor
    · rintro ⟨r, hr, v, ⟨u, hu, rfl⟩, rfl⟩
      exact ⟨r, hr, e u, ⟨sphereRotation e u, hu, rfl⟩, by simp⟩
    · rintro ⟨r, hr, v, ⟨u, hu, rfl⟩, he⟩
      refine ⟨r, hr, e.symm u, ⟨(sphereRotation e).symm u, ?_, rfl⟩, ?_⟩
      · simpa using hu
      · apply e.injective
        simpa using he
  rw [hset]
  have he := e.measurePreserving.map_eq
  have hm := e.toMeasurableEquiv.measurableEmbedding.map_apply volume
    (Ioo (0 : ℝ) 1 • (Subtype.val '' s))
  simp only [LinearIsometryEquiv.coe_toMeasurableEquiv] at hm
  rw [he] at hm
  exact hm.symm

omit [Nontrivial V] in
lemma sphereRotation_preserves_probability (e : V ≃ₗᵢ[ℝ] V) :
    MeasurePreserving (sphereRotation e) (sphereProbability V) (sphereProbability V) := by
  exact (sphereRotation_preserves_toSphere e).smul_measure _

omit [Nontrivial V] in
lemma integral_sphere_rotation (e : V ≃ₗᵢ[ℝ] V) (g : UnitSphere V → ℝ) :
    (∫ x, g (sphereRotation e x) ∂sphereProbability V) =
      ∫ x, g x ∂sphereProbability V :=
  (sphereRotation_preserves_probability e).integral_comp
    (sphereRotation e).measurableEmbedding g

end SphereMeasure

end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_SphereGeometry_IntegralLift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace ContDiff
open scoped Manifold
open MeasureTheory Set Metric
open scoped ENNReal Pointwise Matrix
section IntegralLift
variable {ν ι : Type*} [Fintype ν] [Nonempty ν] [Fintype ι]
local notation "E" => EuclideanSpace ℝ ν

omit [Nonempty ν] in
lemma Admissible.integrand_continuous {f : E → ι → ℝ} (hf : Admissible f)
    (T : E →L[ℝ] E) (i : ι) :
    Continuous (fun x : UnitSphere E => homogeneousLift f (T x) i) :=
  (continuous_apply i).comp (hf.lift_continuous.comp (T.continuous.comp continuous_subtype_val))

lemma Admissible.integrand_integrable {f : E → ι → ℝ} (hf : Admissible f)
    (T : E →L[ℝ] E) (i : ι) :
    Integrable (fun x : UnitSphere E => homogeneousLift f (T x) i) (sphereProbability E) :=
  (hf.integrand_continuous T i).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

omit [Nonempty ν] in
lemma Admissible.integralLift_nonneg {f : E → ι → ℝ} (hf : Admissible f)
    (T : E →L[ℝ] E) (i : ι) : 0 ≤ integralLift f T i :=
  mul_nonneg (Nat.cast_nonneg _) (integral_nonneg (fun _ => hf.lift_nonneg _ i))

lemma Admissible.integralLift_sum {f : E → ι → ℝ} (hf : Admissible f)
    (T : E →L[ℝ] E) : ∑ i, integralLift f T i =
      (Fintype.card ν : ℝ) * ∫ x : UnitSphere E, ‖T x‖ ^ 2 ∂sphereProbability E := by
  classical
  simp only [integralLift, ← Finset.mul_sum]
  rw [← integral_finsetSum _ (fun i _ => hf.integrand_integrable T i)]
  simp only [hf.lift_sum]

lemma Admissible.integralLift_pos_iff_sphere {f : E → ι → ℝ} (hf : Admissible f)
    (T : E →L[ℝ] E) (i : ι) :
    0 < integralLift f T i ↔ ∃ x : UnitSphere E, 0 < homogeneousLift f (T x) i := by
  have hc : (0 : ℝ) < Fintype.card ν := Nat.cast_pos.mpr Fintype.card_pos
  rw [integralLift, mul_pos_iff_of_pos_left hc]
  constructor
  · intro h
    by_contra hn
    push Not at hn
    have he : (fun x : UnitSphere E => homogeneousLift f (T x) i) = 0 := by
      funext x
      exact le_antisymm (hn x) (hf.lift_nonneg _ i)
    rw [he] at h
    change 0 < ∫ _ : UnitSphere E, (0 : ℝ) ∂sphereProbability E at h
    simp only [integral_zero, lt_self_iff_false] at h
  · rintro ⟨x, hx⟩
    exact integral_pos_of_integrable_nonneg_nonzero (hf.integrand_continuous T i)
      (hf.integrand_integrable T i) (fun _ => hf.lift_nonneg _ i) hx.ne'

lemma Admissible.integralLift_continuous {f : E → ι → ℝ} (hf : Admissible f) :
    Continuous (integralLift f) := by
  apply continuous_pi
  intro i
  apply continuous_const.mul
  have hc : Continuous (fun p : (E →L[ℝ] E) × UnitSphere E =>
      homogeneousLift f (p.1 p.2) i) :=
    (continuous_apply i).comp (hf.lift_continuous.comp
      (continuous_fst.clm_apply (continuous_subtype_val.comp continuous_snd)))
  have hi := continuous_parametric_integral_of_continuous
    (μ := sphereProbability E)
    (f := fun (T : E →L[ℝ] E) (x : UnitSphere E) => homogeneousLift f (T x) i)
    hc isCompact_univ
  simpa only [setIntegral_univ] using hi

lemma Admissible.integralLift_pos_iff {f : E → ι → ℝ} (hf : Admissible f)
    (T : E →L[ℝ] E) (i : ι) :
    0 < integralLift f T i ↔ ∃ x : E, 0 < homogeneousLift f (T x) i := by
  rw [hf.integralLift_pos_iff_sphere]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, hx⟩
  · rintro ⟨x, hx⟩
    have hx0 : x ≠ 0 := by
      rintro rfl
      simp at hx
    have hn : 0 < ‖x‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr hx0)
    refine ⟨⟨‖x‖⁻¹ • x, mem_sphere_zero_iff_norm.mpr (norm_smul_inv_norm (𝕜 := ℝ) hx0)⟩, ?_⟩
    simp only [map_smul, homogeneousLift_smul_pos f _ hn, Pi.smul_apply, smul_eq_mul]
    exact mul_pos (sq_pos_of_pos hn) hx

lemma Admissible.integralLift_support {f : E → ι → ℝ} (hf : Admissible f)
    (T : E →L[ℝ] E) (i : ι) :
    0 < integralLift f T i ↔ ∃ v : E,
      v ∈ LinearMap.range T.toLinearMap ∧ ‖v‖ = 1 ∧ 0 < f v i := by
  rw [hf.integralLift_pos_iff]
  constructor
  · rintro ⟨x, hx⟩
    have hx0 : T x ≠ 0 := by
      intro hz
      simp only [hz, homogeneousLift_zero, Pi.zero_apply, lt_self_iff_false] at hx
    refine ⟨‖T x‖⁻¹ • T x, ⟨‖T x‖⁻¹ • x, by simp⟩,
      norm_smul_inv_norm (𝕜 := ℝ) hx0, ?_⟩
    exact (mul_pos_iff_of_pos_left (sq_pos_of_pos (norm_pos_iff.mpr hx0))).mp hx
  · rintro ⟨v, ⟨x, rfl⟩, hv, hx⟩
    refine ⟨x, ?_⟩
    rw [homogeneousLift_unit f (show ‖T x‖ = 1 from hv)]
    exact hx

end IntegralLift

end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_SphereGeometry_SphereMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace ContDiff
open scoped Manifold
open MeasureTheory Set Metric
open scoped ENNReal Pointwise Matrix
section SphereMoments
variable {ι : Type*} [Fintype ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι

lemma sphere_coord_integrable (i j : ι) :
    Integrable (fun x : UnitSphere E => (x : E) i * (x : E) j) (sphereProbability E) := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact ((PiLp.continuous_apply 2 _ i).comp continuous_subtype_val).mul
      ((PiLp.continuous_apply 2 _ j).comp continuous_subtype_val)
  · exact HasCompactSupport.of_compactSpace _

omit [Nonempty ι] in
lemma sphere_coord_cross {i j : ι} (hij : i ≠ j) :
    (∫ x : UnitSphere E, (x : E) i * (x : E) j ∂sphereProbability E) = 0 := by
  classical
  let e : E ≃ₗᵢ[ℝ] E := LinearIsometryEquiv.piLpCongrRight 2
    (fun k => if k = i then LinearIsometryEquiv.neg ℝ else LinearIsometryEquiv.refl ℝ ℝ)
  have hi := integral_sphere_rotation e (fun x : UnitSphere E => (x : E) i * (x : E) j)
  have he : (fun x : UnitSphere E => (sphereRotation e x : E) i * (sphereRotation e x : E) j) =
      fun x : UnitSphere E => -((x : E) i * (x : E) j) := by
    funext x
    simp [sphereRotation, e, hij.symm]
  rw [he, integral_neg] at hi
  linarith

omit [Nonempty ι] in
lemma sphere_coord_diag_eq (i j : ι) :
    (∫ x : UnitSphere E, (x : E) i * (x : E) i ∂sphereProbability E) =
      ∫ x : UnitSphere E, (x : E) j * (x : E) j ∂sphereProbability E := by
  classical
  let e : E ≃ₗᵢ[ℝ] E := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap i j)
  have hi := integral_sphere_rotation e (fun x : UnitSphere E => (x : E) j * (x : E) j)
  convert hi using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ext x
  simp [sphereRotation, e, Equiv.piCongrLeft']

lemma sphere_coord_diag (i : ι) :
    (∫ x : UnitSphere E, (x : E) i * (x : E) i ∂sphereProbability E) =
      (Fintype.card ι : ℝ)⁻¹ := by
  classical
  have hs : (∑ j, ∫ x : UnitSphere E, (x : E) j * (x : E) j ∂sphereProbability E) = 1 := by
    rw [← integral_finsetSum _ (fun j _ => sphere_coord_integrable j j)]
    have he : (fun x : UnitSphere E => ∑ j, (x : E) j * (x : E) j) = fun _ => (1 : ℝ) := by
      funext x
      have hn : ‖(x : E)‖ = 1 := mem_sphere_zero_iff_norm.mp x.property
      have hh := EuclideanSpace.real_norm_sq_eq (x : E)
      rw [hn] at hh
      simpa only [one_pow, pow_two, one_mul] using hh.symm
    rw [he]
    simp
  have hval : (Fintype.card ι : ℝ) *
      (∫ x : UnitSphere E, (x : E) i * (x : E) i ∂sphereProbability E) = 1 := by
    rw [← hs]
    rw [Finset.sum_congr rfl (fun j _ => sphere_coord_diag_eq j i)]
    simp
  exact eq_inv_of_mul_eq_one_right hval

lemma sphere_quadratic_integral (A : Matrix ι ι ℝ) :
    (∫ x : UnitSphere E, (x : E).ofLp ⬝ᵥ A *ᵥ (x : E).ofLp ∂sphereProbability E) =
      Matrix.trace A * (Fintype.card ι : ℝ)⁻¹ := by
  classical
  have hc (i j : ι) : Integrable (fun x : UnitSphere E =>
      A i j * ((x : E) i * (x : E) j)) (sphereProbability E) :=
    (sphere_coord_integrable i j).const_mul _
  have he : (fun x : UnitSphere E => (x : E).ofLp ⬝ᵥ A *ᵥ (x : E).ofLp) =
      fun x : UnitSphere E => ∑ i, ∑ j, A i j * ((x : E) i * (x : E) j) := by
    funext x
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he, integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hc i j))]
  simp_rw [integral_finsetSum _ (fun j _ => hc _ j), integral_const_mul]
  calc
    _ = ∑ i, A i i * (Fintype.card ι : ℝ)⁻¹ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_eq_single i]
      · rw [sphere_coord_diag]
      · intro j _ hji
        rw [sphere_coord_cross hji.symm, mul_zero]
      · simp
    _ = _ := by rw [← Finset.sum_mul]; rfl

end SphereMoments

end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_MatrixGeometry_MatrixKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace ContDiff
open scoped Manifold
open MeasureTheory Set Metric
open scoped ENNReal Pointwise Matrix
section MatrixKernel
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {ν : Type*} [Fintype ν] [DecidableEq ν]
local notation "Ek" => EuclideanSpace ℝ ν
local notation "op" => Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)

lemma matrix_image_orthogonal_kernel {A : Matrix ν ν ℝ} (hA : IsSelfAdjoint A)
    {x : Ek} (hx : op A x = 0) (y : Ek) : ⟪x, op A y⟫ = 0 := by
  rw [← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.star_eq_adjoint,
    ← map_star, hA.star_eq, hx, inner_zero_left]

end MatrixKernel

section PositiveExtension
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {ν ι : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν] [Fintype ι]
local notation "E" => EuclideanSpace ℝ ν
local notation "op" => Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)

omit [Nonempty ν] in
lemma Admissible.positiveExtension_nonneg {f : E → ι → ℝ} (hf : Admissible f)
    (Q : Matrix ν ν ℝ) (i : ι) : 0 ≤ positiveExtension f Q i :=
  hf.integralLift_nonneg _ _

lemma Admissible.positiveExtension_sum {f : E → ι → ℝ} (hf : Admissible f)
    {Q : Matrix ν ν ℝ} (hQ : 0 ≤ Q) : ∑ i, positiveExtension f Q i = Matrix.trace Q := by
  classical
  rw [positiveExtension, hf.integralLift_sum]
  simp_rw [sqrt_action_norm_sq Q hQ, Matrix.inner_toEuclideanCLM]
  rw [sphere_quadratic_integral]
  have hn : (Fintype.card ν : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt Fintype.card_pos)
  field_simp

lemma Admissible.positiveExtension_continuousOn {f : E → ι → ℝ} (hf : Admissible f) :
    ContinuousOn (positiveExtension f) {Q : Matrix ν ν ℝ | 0 ≤ Q} := by
  have hc : Continuous (fun Q : Matrix ν ν ℝ => op Q) :=
    (op).toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional
  exact hf.integralLift_continuous.comp_continuousOn
    (hc.comp_continuousOn CFC.continuousOn_sqrt)

lemma Admissible.positiveExtension_support {f : E → ι → ℝ} (hf : Admissible f)
    {Q : Matrix ν ν ℝ} (hQ : 0 ≤ Q) (i : ι) :
    0 < positiveExtension f Q i ↔ ∃ v : E,
      v ∈ LinearMap.range (op Q).toLinearMap ∧ ‖v‖ = 1 ∧ 0 < f v i := by
  rw [positiveExtension, hf.integralLift_support, matrix_sqrt_range Q hQ]

end PositiveExtension

end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_MatrixGeometry_SignedExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace ContDiff
open scoped Manifold
open MeasureTheory Set Metric
open scoped ENNReal Pointwise Matrix
section SignedExtension
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {ν ι : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν] [Fintype ι]
local notation "E" => EuclideanSpace ℝ ν
local notation "op" => Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)

omit [Nonempty ν] in
lemma matrix_images_orthogonal {P N : Matrix ν ν ℝ} (hP : 0 ≤ P) (hPN : P * N = 0)
    (x y : E) : ⟪op P x, op N y⟫ = 0 := by
  rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint]
  have hs : star (op P) = op P := by rw [← map_star, hP.star_eq]
  rw [hs]
  change ⟪x, (op P * op N) y⟫ = 0
  rw [← map_mul, hPN, map_zero]
  simp

lemma Admissible.positiveExtension_orthogonal {f : E → ι → ℝ} (hf : Admissible f)
    {P N : Matrix ν ν ℝ} (hP : 0 ≤ P) (hN : 0 ≤ N) (hPN : P * N = 0) (i : ι) :
    positiveExtension f P i * positiveExtension f N i = 0 := by
  apply mul_eq_zero.mpr
  by_contra hn
  push Not at hn
  have hp := lt_of_le_of_ne (hf.positiveExtension_nonneg P i) (Ne.symm hn.1)
  have hn' := lt_of_le_of_ne (hf.positiveExtension_nonneg N i) (Ne.symm hn.2)
  obtain ⟨v, ⟨x, rfl⟩, hv, hx⟩ := (hf.positiveExtension_support hP i).mp hp
  obtain ⟨w, ⟨y, rfl⟩, hw, hy⟩ := (hf.positiveExtension_support hN i).mp hn'
  exact hf.orthogonal _ _ hv hw (matrix_images_orthogonal hP hPN x y) i ⟨hx, hy⟩

omit [Nonempty ν] [Fintype ι] in
lemma signedExtension_odd (f : E → ι → ℝ) (A : Matrix ν ν ℝ) :
    signedExtension f (-A) = -signedExtension f A := by
  simp [signedExtension, CFC.posPart_neg, CFC.negPart_neg]

lemma Admissible.signedExtension_abs_sum {f : E → ι → ℝ} (hf : Admissible f)
    {A : Matrix ν ν ℝ} (hA : IsSelfAdjoint A) :
    ∑ i, |signedExtension f A i| = Matrix.trace (CFC.abs A) := by
  classical
  have hcoord (i : ι) : |signedExtension f A i| =
      positiveExtension f A⁺ i + positiveExtension f A⁻ i := by
    have hp := hf.positiveExtension_nonneg A⁺ i
    have hn := hf.positiveExtension_nonneg A⁻ i
    have hprod := hf.positiveExtension_orthogonal (CFC.posPart_nonneg A)
      (CFC.negPart_nonneg A) (CFC.posPart_mul_negPart A) i
    rcases mul_eq_zero.mp hprod with hz | hz
    · simp [signedExtension, hz, abs_of_nonneg hn]
    · simp [signedExtension, hz, abs_of_nonneg hp]
  simp_rw [hcoord]
  rw [Finset.sum_add_distrib, hf.positiveExtension_sum (CFC.posPart_nonneg A),
    hf.positiveExtension_sum (CFC.negPart_nonneg A), ← Matrix.trace_add,
    CFC.posPart_add_negPart A hA]

omit [Nonempty ν] in
lemma matrix_posPart_continuousOn :
    ContinuousOn (fun A : Matrix ν ν ℝ => A⁺) {A | IsSelfAdjoint A} := by
  have hc : Continuous (fun A : Matrix ν ν ℝ => (1 / 2 : ℝ) • (CFC.abs A + A)) :=
    (continuous_const (y := (1 / 2 : ℝ))).smul (CFC.continuous_abs.add continuous_id)
  apply hc.continuousOn.congr
  intro A hA
  change A⁺ = (1 / 2 : ℝ) • (CFC.abs A + A)
  rw [CFC.abs_add_self A hA, two_smul, smul_add]
  module

omit [Nonempty ν] in
lemma matrix_negPart_continuousOn :
    ContinuousOn (fun A : Matrix ν ν ℝ => A⁻) {A | IsSelfAdjoint A} := by
  have hc : Continuous (fun A : Matrix ν ν ℝ => (1 / 2 : ℝ) • (CFC.abs A - A)) :=
    (continuous_const (y := (1 / 2 : ℝ))).smul (CFC.continuous_abs.sub continuous_id)
  apply hc.continuousOn.congr
  intro A hA
  change A⁻ = (1 / 2 : ℝ) • (CFC.abs A - A)
  rw [CFC.abs_sub_self A hA, two_smul, smul_add]
  module

lemma Admissible.signedExtension_continuousOn {f : E → ι → ℝ} (hf : Admissible f) :
    ContinuousOn (signedExtension f) {A : Matrix ν ν ℝ | IsSelfAdjoint A} := by
  apply ContinuousOn.sub
  · exact hf.positiveExtension_continuousOn.comp matrix_posPart_continuousOn
      (fun A _ => CFC.posPart_nonneg A)
  · exact hf.positiveExtension_continuousOn.comp matrix_negPart_continuousOn
      (fun A _ => CFC.negPart_nonneg A)

end SignedExtension

end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Support_FullSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace ContDiff
open scoped Manifold
open MeasureTheory Set Metric
open scoped ENNReal Pointwise Matrix
section FullSupport
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {ν ι : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν] [Fintype ι]

omit [Nonempty ν] in
lemma matrix_psd_trace_zero {Q : Matrix ν ν ℝ} (hQ : 0 ≤ Q)
    (htrace : Matrix.trace Q = 0) : Q = 0 := by
  have hprod : (CFC.sqrt Q)ᴴ * CFC.sqrt Q = Q := by
    rw [← Matrix.star_eq_conjTranspose, (CFC.sqrt_nonneg Q).star_eq, CFC.sqrt_mul_sqrt_self Q hQ]
  have hz : CFC.sqrt Q = 0 := Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp
    (hprod.symm ▸ htrace)
  rw [← hprod, hz]
  simp

end FullSupport

end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_SphereGeometry_SphereExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace ContDiff
open scoped Manifold
open MeasureTheory Set Metric
open scoped ENNReal Pointwise Matrix
section SphereExtension
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {ν ι : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν] [Fintype ι]
local notation "E" => EuclideanSpace ℝ ν

lemma Admissible.signedExtension_eq_zero_iff {f : E → ι → ℝ} (hf : Admissible f)
    {A : Matrix ν ν ℝ} (hA : IsSelfAdjoint A) : signedExtension f A = 0 ↔ A = 0 := by
  constructor
  · intro hz
    have ht : Matrix.trace (CFC.abs A) = 0 := by
      rw [← hf.signedExtension_abs_sum hA, hz]
      simp
    have habs : CFC.abs A = 0 := matrix_psd_trace_zero (CFC.abs_nonneg A) ht
    have hsq := CFC.abs_mul_abs A
    rw [habs, zero_mul] at hsq
    apply Matrix.conjTranspose_mul_self_eq_zero.mp
    simpa only [Matrix.star_eq_conjTranspose] using hsq.symm
  · rintro rfl
    simp [signedExtension]

end SphereExtension

end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Simplicial_UnitRadial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset
open scoped RealInnerProductSpace

lemma unitRadial_norm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x : E} (hx : x ≠ 0) : ‖unitRadial x‖ = 1 := by
  rw [unitRadial, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]

end BorsukNine.SimplicialChains

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_SphereGeometry_HemisphereChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine
open scoped RealInnerProductSpace
open SimplicialChains
section HemisphereChart
variable {E W : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
variable (w : E) (e : W →ₗᵢ[ℝ] E)

lemma adjoint_isometry_apply (v : W) : e.toContinuousLinearMap.adjoint (e v) = v := by
  have hh := congrArg (fun T : W →L[ℝ] W => T v) e.adjoint_comp_self
  exact hh

lemma adjoint_normal (he : ∀ v, ⟪w,e v⟫ = 0) : e.toContinuousLinearMap.adjoint w = 0 := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_zero_left,ContinuousLinearMap.adjoint_inner_left]
  exact he v

lemma frame_decomposition (hw : ‖w‖ = 1)
    (he : ∀ v, ⟪w,e v⟫ = 0) (hes : ∀ u, ⟪w,u⟫ = 0 → ∃ v, e v = u) (u : E) :
    e (e.toContinuousLinearMap.adjoint u) = u - ⟪w,u⟫ • w := by
  obtain ⟨v,hv⟩ := hes (u - ⟪w,u⟫ • w) (by simp [inner_sub_right,inner_smul_right,hw])
  have ha := congrArg e.toContinuousLinearMap.adjoint hv
  rw [adjoint_isometry_apply,map_sub,map_smul,adjoint_normal w e he,smul_zero,sub_zero] at ha
  rw [← ha,hv]

omit [CompleteSpace E] [CompleteSpace W] in
lemma hemisphere_add_ne_zero (hw : ‖w‖ = 1) (he : ∀ v, ⟪w,e v⟫ = 0) (v : W) :
    w + e v ≠ 0 := by
  intro hz
  have h := congrArg (fun u => ⟪w,u⟫) hz
  simp [inner_add_right,he,hw] at h

omit [CompleteSpace E] [CompleteSpace W] in
lemma hemisphereChart_contDiff (hw : ‖w‖ = 1) (he : ∀ v, ⟪w,e v⟫ = 0) :
    ContDiff ℝ (⊤ : ℕ∞) (hemisphereChart w e) := by
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun v => w + e v) := contDiff_const.add e.contDiff
  exact (hc.norm ℝ (hemisphere_add_ne_zero w e hw he)).inv
    (fun v => norm_ne_zero_iff.mpr (hemisphere_add_ne_zero w e hw he v)) |>.smul hc

omit [CompleteSpace E] [CompleteSpace W] in
lemma hemisphereChart_norm (hw : ‖w‖ = 1) (he : ∀ v, ⟪w,e v⟫ = 0) (v : W) :
    ‖hemisphereChart w e v‖ = 1 := unitRadial_norm (hemisphere_add_ne_zero w e hw he v)

lemma hemisphereInverse_chart (hw : ‖w‖ = 1) (he : ∀ v, ⟪w,e v⟫ = 0) (v : W) :
    hemisphereInverse w e (hemisphereChart w e v) = v := by
  have hn : ‖w + e v‖ ≠ 0 := norm_ne_zero_iff.mpr (hemisphere_add_ne_zero w e hw he v)
  simp only [hemisphereInverse,hemisphereChart,unitRadial,inner_smul_right,inner_add_right,
    real_inner_self_eq_norm_sq,hw,one_pow,he,add_zero,mul_one,inv_inv,map_smul,map_add,
    adjoint_normal w e he,adjoint_isometry_apply,zero_add,smul_smul,mul_inv_cancel₀ hn,one_smul]

lemma hemisphereChart_inverse (hw : ‖w‖ = 1) (he : ∀ v, ⟪w,e v⟫ = 0)
    (hes : ∀ u, ⟪w,u⟫ = 0 → ∃ v, e v = u) {u : E} (hu : ‖u‖ = 1) (hwu : 0 < ⟪w,u⟫) :
    hemisphereChart w e (hemisphereInverse w e u) = u := by
  have heq : w + e (hemisphereInverse w e u) = ⟪w,u⟫⁻¹ • u := by
    rw [hemisphereInverse,map_smul,frame_decomposition w e hw he hes,smul_sub,smul_smul,
      inv_mul_cancel₀ (ne_of_gt hwu),one_smul]
    abel
  rw [hemisphereChart,heq,unitRadial,norm_smul,Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hwu),hu,mul_one,inv_inv,smul_smul,
    mul_inv_cancel₀ (ne_of_gt hwu),one_smul]

lemma hemisphereInverse_continuousOn :
    ContinuousOn (hemisphereInverse w e) {u | 0 < ⟪w,u⟫} :=
  ((continuous_const.inner continuous_id).continuousOn.inv₀ (fun _ h => ne_of_gt h)).smul
    e.toContinuousLinearMap.adjoint.continuous.continuousOn
end HemisphereChart
end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_LocalParity_ChartRegular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine
open scoped RealInnerProductSpace Topology
open Filter
section ChartRegular
variable {E W : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W] [FiniteDimensional ℝ W]
omit [CompleteSpace E] [CompleteSpace W] [FiniteDimensional ℝ W] in
lemma hemisphereChart_zero {c : E} (hc : ‖c‖ = 1) (e : W →ₗᵢ[ℝ] E) : hemisphereChart c e 0 = c := by
  simp [hemisphereChart,SimplicialChains.unitRadial,hc]
omit [FiniteDimensional ℝ W] in
lemma hemisphereInverse_contDiffAt (w : E) (e : W →ₗᵢ[ℝ] E) {u : E} (hu : ⟪w,u⟫ ≠ 0) :
    ContDiffAt ℝ (⊤ : ℕ∞) (hemisphereInverse w e) u :=
  ((contDiffAt_const.inner ℝ contDiffAt_id).inv hu).smul e.toContinuousLinearMap.adjoint.contDiff.contDiffAt

omit [FiniteDimensional ℝ W] in
lemma hemisphere_transition_regular {w c : E} (hw : ‖w‖ = 1) (hc : ‖c‖ = 1)
    (e d : W →ₗᵢ[ℝ] E) (he : ∀ v, ⟪w,e v⟫ = 0) (hd : ∀ v, ⟪c,d v⟫ = 0)
    (hes : ∀ u, ⟪w,u⟫ = 0 → ∃ v, e v = u) (_hds : ∀ u, ⟪c,u⟫ = 0 → ∃ v, d v = u)
    (hwc : 0 < ⟪w,c⟫) (f : E → W) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hr : (fderiv ℝ (fun v => f (hemisphereChart w e v)) (hemisphereInverse w e c)).det ≠ 0) :
    (fderiv ℝ (fun v => f (hemisphereChart c d v)) 0).det ≠ 0 := by
  let T : W → W := fun v => hemisphereInverse w e (hemisphereChart c d v)
  let S : W → W := fun v => hemisphereInverse c d (hemisphereChart w e v)
  let v₀ := hemisphereInverse w e c
  have hTc : T 0 = v₀ := by simp [T,v₀,hemisphereChart_zero hc]
  have hwc' : hemisphereChart w e v₀ = c := hemisphereChart_inverse w e hw he hes hc hwc
  have hT : ContDiffAt ℝ (⊤ : ℕ∞) T 0 :=
    (hemisphereInverse_contDiffAt w e (by simpa only [hemisphereChart_zero hc] using ne_of_gt hwc)).comp 0
      (hemisphereChart_contDiff c d hc hd).contDiffAt
  have hS : ContDiffAt ℝ (⊤ : ℕ∞) S v₀ :=
    (hemisphereInverse_contDiffAt c d (by rw [hwc']; simp [hc])).comp v₀
      (hemisphereChart_contDiff w e hw he).contDiffAt
  have hnear : ∀ᶠ v in 𝓝 (0:W), 0 < ⟪w,hemisphereChart c d v⟫ :=
    (continuous_const.inner (hemisphereChart_contDiff c d hc hd).continuous).continuousAt
      (isOpen_Ioi.mem_nhds (by simpa only [hemisphereChart_zero hc,Set.mem_Ioi] using hwc))
  have hST : (fun v => S (T v)) =ᶠ[𝓝 (0:W)] id := by
    filter_upwards [hnear] with v hv
    dsimp [S,T]
    rw [hemisphereChart_inverse w e hw he hes (hemisphereChart_norm c d hc hd v) hv,
      hemisphereInverse_chart c d hc hd]
  have hdT := hT.differentiableAt (by simp)
  have hdS := hS.differentiableAt (by simp)
  have hdS' : HasFDerivAt S (fderiv ℝ S v₀) (T 0) := by rw [hTc]; exact hdS.hasFDerivAt
  have hcomp : (fderiv ℝ S v₀).comp (fderiv ℝ T 0) = ContinuousLinearMap.id ℝ W :=
    (hdS'.comp 0 hdT.hasFDerivAt).unique ((hasFDerivAt_id (0:W)).congr_of_eventuallyEq hST)
  have hTdet : (fderiv ℝ T 0).det ≠ 0 := by
    have composition_det := congrArg ContinuousLinearMap.det hcomp
    change LinearMap.det ((fderiv ℝ S v₀).toLinearMap.comp (fderiv ℝ T 0).toLinearMap) =
      LinearMap.det (LinearMap.id : W →ₗ[ℝ] W) at composition_det
    rw [LinearMap.det_comp, LinearMap.det_id] at composition_det
    have nonzero_product : (fderiv ℝ S v₀).det * (fderiv ℝ T 0).det ≠ 0 := by
      rw [composition_det]
      exact one_ne_zero
    exact (mul_ne_zero_iff.mp nonzero_product).2
  let g : W → W := fun v => f (hemisphereChart w e v)
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := hf.comp (hemisphereChart_contDiff w e hw he)
  have hfg : (fun v => f (hemisphereChart c d v)) =ᶠ[𝓝 (0:W)] (fun v => g (T v)) := by
    filter_upwards [hnear] with v hv
    dsimp [g,T]
    rw [hemisphereChart_inverse w e hw he hes (hemisphereChart_norm c d hc hd v) hv]
  have hgT : HasFDerivAt g (fderiv ℝ g v₀) (T 0) := by
    rw [hTc]
    exact (hg.differentiable (by simp) v₀).hasFDerivAt
  have hfinal := (hgT.comp 0 hdT.hasFDerivAt).congr_of_eventuallyEq hfg
  rw [hfinal.fderiv]
  change LinearMap.det ((fderiv ℝ g v₀).toLinearMap.comp (fderiv ℝ T 0).toLinearMap) ≠ 0
  rw [LinearMap.det_comp]
  exact mul_ne_zero hr hTdet
end ChartRegular
end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Support_DisjointChambers
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped Matrix RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
section MatrixEmbedding
variable {μ ν : Type*} [Fintype μ] [Fintype ν] [DecidableEq μ] [DecidableEq ν]
local notation "D" => EuclideanSpace ℝ μ
local notation "E" => EuclideanSpace ℝ ν

lemma toEuclideanLin_mul {α β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]
    (A : Matrix α β ℝ) (B : Matrix β γ ℝ) :
    Matrix.toEuclideanLin (A*B) = (Matrix.toEuclideanLin A).comp (Matrix.toEuclideanLin B) := by
  apply LinearMap.ext
  intro v
  apply PiLp.ext
  intro i
  change ((A*B)*ᵥ v) i = (A *ᵥ (B *ᵥ v)) i
  rw [Matrix.mulVec_mulVec]

omit [DecidableEq ν] in
lemma isometryMatrix_action (e : D →ₗᵢ[ℝ] E) (x : D) :
    Matrix.toEuclideanLin (isometryMatrix e) x = e x :=
  LinearMap.congr_fun (Matrix.toEuclideanLin.apply_symm_apply e.toLinearMap) x

lemma isometryMatrix_star_mul (e : D →ₗᵢ[ℝ] E) :
    (isometryMatrix e)ᴴ * isometryMatrix e = 1 := by
  apply Matrix.toEuclideanLin.injective
  rw [toEuclideanLin_mul,Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  have he : Matrix.toEuclideanLin (isometryMatrix e) = e.toLinearMap :=
    Matrix.toEuclideanLin.apply_symm_apply _
  rw [he]
  rw [e.adjoint_comp_self']
  apply LinearMap.ext
  intro x
  simp only [LinearMap.id_apply,Matrix.toLpLin_apply,Matrix.one_mulVec,WithLp.toLp_ofLp]

lemma matrixEmbed_action (e : D →ₗᵢ[ℝ] E) (B : Matrix μ μ ℝ) (x : D) :
    Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ) (matrixEmbed e B) (e x) =
      e (Matrix.toEuclideanCLM (n := μ) (𝕜 := ℝ) B x) := by
  change Matrix.toEuclideanLin (matrixEmbed e B) (e x) = e (Matrix.toEuclideanLin B x)
  change Matrix.toEuclideanLin (isometryMatrix e * B * (isometryMatrix e)ᴴ) (e x) = _
  rw [toEuclideanLin_mul,toEuclideanLin_mul]
  change Matrix.toEuclideanLin (isometryMatrix e)
    (Matrix.toEuclideanLin B (Matrix.toEuclideanLin (isometryMatrix e)ᴴ (e x))) = _
  have hh : Matrix.toEuclideanLin (isometryMatrix e)ᴴ (e x) = x := by
    rw [← isometryMatrix_action e x]
    change ((Matrix.toEuclideanLin (isometryMatrix e)ᴴ).comp
      (Matrix.toEuclideanLin (isometryMatrix e))) x = x
    rw [← toEuclideanLin_mul,isometryMatrix_star_mul]
    simp only [Matrix.toLpLin_apply,Matrix.one_mulVec,WithLp.toLp_ofLp]
  rw [hh,isometryMatrix_action]

end MatrixEmbedding
end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_MatrixGeometry_MatrixCompression
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped Matrix RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
section MatrixCompression
variable {μ ν : Type*} [Fintype μ] [Fintype ν] [DecidableEq μ] [DecidableEq ν]
local notation "D" => EuclideanSpace ℝ μ
local notation "E" => EuclideanSpace ℝ ν

omit [DecidableEq ν] in
lemma matrixCompress_nonneg (e : D →ₗᵢ[ℝ] E) {Q : Matrix ν ν ℝ} (hQ : 0 ≤ Q) :
    0 ≤ matrixCompress e Q :=
  ((Matrix.nonneg_iff_posSemidef.mp hQ).conjTranspose_mul_mul_same _).nonneg

lemma isometryMatrix_adjoint_action (e : D →ₗᵢ[ℝ] E) (x : D) :
    Matrix.toEuclideanLin (isometryMatrix e)ᴴ (e x) = x := by
  rw [← isometryMatrix_action e x]
  change ((Matrix.toEuclideanLin (isometryMatrix e)ᴴ).comp
    (Matrix.toEuclideanLin (isometryMatrix e))) x = x
  rw [← toEuclideanLin_mul,isometryMatrix_star_mul]
  simp only [Matrix.toLpLin_apply,Matrix.one_mulVec,WithLp.toLp_ofLp]

lemma matrixEmbed_compress (e : D →ₗᵢ[ℝ] E) {Q : Matrix ν ν ℝ}
    (hQ : IsSelfAdjoint Q)
    (hR : LinearMap.range (Matrix.toEuclideanLin Q) ≤ LinearMap.range e.toLinearMap) :
    matrixEmbed e (matrixCompress e Q) = Q := by
  let T := isometryMatrix e
  have hleft : (T * Tᴴ) * Q = Q := by
    apply Matrix.toEuclideanLin.injective
    apply LinearMap.ext
    intro v
    obtain ⟨x,hx⟩ := hR (LinearMap.mem_range_self (Matrix.toEuclideanLin Q) v)
    change e x = Matrix.toEuclideanLin Q v at hx
    rw [toEuclideanLin_mul,toEuclideanLin_mul]
    change Matrix.toEuclideanLin T (Matrix.toEuclideanLin Tᴴ (Matrix.toEuclideanLin Q v)) = _
    rw [← hx,isometryMatrix_adjoint_action,isometryMatrix_action]
  have hright : Q * (T*Tᴴ) = Q := by
    have he := congrArg Matrix.conjTranspose hleft
    rw [Matrix.conjTranspose_mul,Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose] at he
    simpa only [← Matrix.star_eq_conjTranspose,hQ.star_eq] using he
  change T * (Tᴴ * Q * T) * Tᴴ = Q
  calc
    _ = ((T*Tᴴ)*Q)*(T*Tᴴ) := by simp only [Matrix.mul_assoc]
    _ = Q := by rw [hleft,hright]

end MatrixCompression

end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Projectors_NegativeQuadratic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory

namespace BorsukNine
open scoped Matrix RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
section MatrixBlocks
variable {μ ν : Type*} [Fintype μ] [Fintype ν] [DecidableEq μ] [DecidableEq ν]
local notation "W" => EuclideanSpace ℝ μ
local notation "E" => EuclideanSpace ℝ ν
local notation "M" => Matrix ν ν ℝ
local notation "op" => Matrix.toEuclideanCLM (𝕜 := ℝ)

omit [DecidableEq ν] in
lemma matrixEmbed_selfAdjoint (e : W →ₗᵢ[ℝ] E) {B : Matrix μ μ ℝ} (hB : IsSelfAdjoint B) :
    IsSelfAdjoint (matrixEmbed e B) := by
  change ((isometryMatrix e) * B * (isometryMatrix e)ᴴ)ᴴ = _
  simp only [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose]
  rw [show Bᴴ = B from hB.star_eq]
  exact (Matrix.mul_assoc _ _ _).symm

omit [DecidableEq ν] in
lemma matrixCompress_selfAdjoint (e : W →ₗᵢ[ℝ] E) {A : M} (hA : IsSelfAdjoint A) :
    IsSelfAdjoint (matrixCompress e A) := by
  change ((isometryMatrix e)ᴴ * A * (isometryMatrix e))ᴴ = _
  simp only [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose]
  rw [show Aᴴ = A from hA.star_eq]
  exact (Matrix.mul_assoc _ _ _).symm

lemma matrixCompress_embed (e : W →ₗᵢ[ℝ] E) (B : Matrix μ μ ℝ) :
    matrixCompress e (matrixEmbed e B) = B := by
  change (isometryMatrix e)ᴴ * (isometryMatrix e * B * (isometryMatrix e)ᴴ) * isometryMatrix e = B
  calc
    _ = ((isometryMatrix e)ᴴ * isometryMatrix e) * B * ((isometryMatrix e)ᴴ * isometryMatrix e) := by
      simp only [Matrix.mul_assoc]
    _ = B := by rw [isometryMatrix_star_mul,Matrix.one_mul,Matrix.mul_one]

lemma isometryMatrix_star_action (e : W →ₗᵢ[ℝ] E) (v : E) :
    Matrix.toEuclideanLin (isometryMatrix e)ᴴ v = e.toContinuousLinearMap.adjoint v := by
  apply ext_inner_left ℝ
  intro x
  rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  change ⟪x,(Matrix.toEuclideanLin (isometryMatrix e)).adjoint v⟫ = _
  rw [LinearMap.adjoint_inner_right,isometryMatrix_action,ContinuousLinearMap.adjoint_inner_right]
  rfl

lemma matrixCompress_action (e : W →ₗᵢ[ℝ] E) (A : M) (v : W) :
    op (matrixCompress e A) v = e.toContinuousLinearMap.adjoint (op A (e v)) := by
  change Matrix.toEuclideanLin ((isometryMatrix e)ᴴ * A * isometryMatrix e) v = _
  rw [toEuclideanLin_mul,toEuclideanLin_mul]
  change Matrix.toEuclideanLin (isometryMatrix e)ᴴ (Matrix.toEuclideanLin A
    (Matrix.toEuclideanLin (isometryMatrix e) v)) = _
  rw [isometryMatrix_action,isometryMatrix_star_action]
  rfl

omit [DecidableEq ν] in
lemma blockCorner_selfAdjoint (e : W →ₗᵢ[ℝ] E) {A : M} (hA : IsSelfAdjoint A) :
    IsSelfAdjoint (blockCorner e A) := matrixEmbed_selfAdjoint e (matrixCompress_selfAdjoint e hA)
lemma blockCorner_of_kernel (e : W →ₗᵢ[ℝ] E) {c : E}
    (hes : ∀ u, ⟪c,u⟫ = 0 → ∃ v, e v = u) {A : M} (hA : IsSelfAdjoint A) (hAc : op A c = 0) :
    blockCorner e A = A := by
  apply matrixEmbed_compress e hA
  rintro _ ⟨x,rfl⟩
  exact hes _ (matrix_image_orthogonal_kernel hA hAc x)

lemma blockScalar_continuous (c : E) : Continuous (blockScalar c : M → ℝ) :=
  continuous_const.inner (((Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)).toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional).clm_apply continuous_const)
omit [DecidableEq μ] in
lemma blockOff_continuous (c : E) (e : W →ₗᵢ[ℝ] E) : Continuous (blockOff c e : M → W) :=
  e.toContinuousLinearMap.adjoint.continuous.comp
    (((Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)).toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional).clm_apply continuous_const)
omit [DecidableEq ν] in
lemma blockCorner_continuous (e : W →ₗᵢ[ℝ] E) : Continuous (blockCorner e : M → M) :=
  (matrixEmbed e).continuous_of_finiteDimensional.comp (matrixCompress e).continuous_of_finiteDimensional

end MatrixBlocks
end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_LocalParity_LocalModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine
open scoped MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
section LocalModel
variable {k : ℕ} {ν ι : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν] [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ ν
local notation "W" => EuclideanSpace ℝ (Fin k)
local notation "M" => Matrix ν ν ℝ

omit [Nonempty ν] [Fintype ι] in
lemma localBlockModel_odd (f : E → ι → ℝ) (c : E) (e : W →ₗᵢ[ℝ] E)
    {I : Finset ι} (a : Fin (k+1) ≃ ↥I) (D : W ≃L[ℝ] W) (A : M) :
    localBlockModel f c e a D (-A) = -localBlockModel f c e a D A := by
  simp only [localBlockModel,blockScalar,blockOff,blockCorner,map_neg,neg_apply,inner_neg_right,neg_smul,
    signedExtension_odd,neg_add_rev]
  abel

lemma Admissible.localBlockModel_continuousOn {f : E → ι → ℝ} (hf : Admissible f)
    (c : E) (e : W →ₗᵢ[ℝ] E) {I : Finset ι} (a : Fin (k+1) ≃ ↥I) (D : W ≃L[ℝ] W) :
    ContinuousOn (localBlockModel f c e a D) {A : M | IsSelfAdjoint A} := by
  apply ContinuousOn.add
  · exact ((blockScalar_continuous c).smul continuous_const).continuousOn.add
      ((facetTangent a).continuous_of_finiteDimensional.comp
        (D.continuous.comp (blockOff_continuous c e))).continuousOn
  · exact hf.signedExtension_continuousOn.comp (blockCorner_continuous e).continuousOn
      (fun A hA => blockCorner_selfAdjoint e hA)

end LocalModel
end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_LocalParity_LocalRegular
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine
open scoped RealInnerProductSpace Topology
section LocalRegular
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
lemma regular_inner_positive (D : E ≃L[ℝ] E) {g : E → E}
    (h0 : g 0 = 0) (hd : HasFDerivAt g D.toContinuousLinearMap 0) :
    ∃ δ > 0, ∀ v, ‖v‖ < δ → v ≠ 0 → 0 < ⟪v,D.symm (g v)⟫ := by
  let H : E → E := fun v => D.symm (g v)
  have hH : HasFDerivAt H (ContinuousLinearMap.id ℝ E) 0 := by
    convert D.symm.hasFDerivAt.comp 0 hd using 1 <;> ext v <;> simp [H]
  have hH0 : H 0 = 0 := by simp [H,h0]
  have herr := hH.isLittleO.def (show (0:ℝ) < 1/2 by norm_num)
  obtain ⟨δ,hδ,hball⟩ := Metric.eventually_nhds_iff.mp herr
  refine ⟨δ,hδ,?_⟩
  intro v hv hv0
  have hb := hball (by simpa only [dist_zero_right] using hv)
  simp only [hH0,sub_zero,ContinuousLinearMap.id_apply] at hb
  have hi : |⟪v,H v - v⟫| ≤ ‖v‖ * ((1/2:ℝ)*‖v‖) :=
    (abs_real_inner_le_norm v _).trans (mul_le_mul_of_nonneg_left hb (norm_nonneg _))
  have hp : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  rw [inner_sub_right,real_inner_self_eq_norm_sq] at hi
  change 0 < ⟪v,H v⟫
  nlinarith [neg_abs_le ⟪v,H v⟫,neg_abs_le (⟪v,H v⟫-‖v‖^2)]

end LocalRegular
end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_LocalParity_Sard
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine
section Sard
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma exists_regular_value (f : E → E) (hf : Differentiable ℝ f)
    {U : Set E} (hU : IsOpen U) (hUn : U.Nonempty) :
    ∃ y ∈ U, ∀ x, f x = y → (fderiv ℝ f x).det ≠ 0 := by
  let μ := (Module.finBasis ℝ E).addHaar
  let C : Set E := {x | (fderiv ℝ f x).det = 0}
  have hz : μ (f '' C) = 0 := addHaar_image_eq_zero_of_det_fderivWithin_eq_zero μ
    (fun x _ => (hf x).hasFDerivAt.hasFDerivWithinAt) (fun _ h => h)
  have hUp : 0 < μ U := hU.measure_pos μ hUn
  have hns : ¬ U ⊆ f '' C := by
    intro hs
    have hh : μ U ≤ μ (f '' C) := measure_mono hs
    rw [hz] at hh
    exact (not_le_of_gt hUp) hh
  obtain ⟨y,hy,hny⟩ := Set.not_subset.mp hns
  refine ⟨y,hy,?_⟩
  intro x hx hc
  exact hny ⟨x,hc,hx⟩

omit [MeasurableSpace E] [BorelSpace E] in
lemma compact_regular_level_finite (f : E → E) (hf : ContDiff ℝ 1 f) {y : E}
    {K : Set E} (hc : IsCompact K) (hK : ∀ x ∈ K, f x = y) (hr : ∀ x, f x = y → (fderiv ℝ f x).det ≠ 0) :
    K.Finite := by
  apply hc.finite
  rw [isDiscrete_iff_forall_mem_exists_isOpen]
  intro x hx
  have hdet := hr x (hK x hx)
  let e : E ≃L[ℝ] E := (LinearMap.equivOfIsUnitDet
    (f := (fderiv ℝ f x).toLinearMap) (isUnit_iff_ne_zero.mpr hdet)).toContinuousLinearEquiv
  have he : e.toContinuousLinearMap = fderiv ℝ f x := by
    ext z
    exact LinearMap.equivOfIsUnitDet_apply _ z
  have hd : HasStrictFDerivAt f e.toContinuousLinearMap x := by
    rw [he]
    exact hf.hasStrictFDerivAt one_ne_zero
  let p := hd.toOpenPartialHomeomorph f
  refine ⟨p.source, p.open_source,?_⟩
  ext z
  constructor
  · intro hz
    exact Set.mem_singleton_iff.mpr (p.injOn hz.1 hd.mem_toOpenPartialHomeomorph_source
      ((hK z hz.2).trans (hK x hx).symm))
  · rintro rfl
    exact ⟨hd.mem_toOpenPartialHomeomorph_source,hx⟩
end Sard
end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_MatrixGeometry_SymmetricEntries
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace
lemma orthogonal_frame (k : ℕ) {u : EuclideanSpace ℝ (Fin (k+1))} (hu : ‖u‖ = 1) :
    ∃ e : EuclideanSpace ℝ (Fin k) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (k+1)),
      (∀ x, ⟪u,e x⟫ = 0) ∧
      (∀ v, ⟪u,v⟫ = 0 → ∃ x, e x = v) := by
  let W := (Submodule.span ℝ {u})ᗮ
  have hu0 : u ≠ 0 := by intro h; simp [h] at hu
  have hdim : Module.finrank ℝ W = k := by
    let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (k+1))) = k+1) := ⟨by simp⟩
    exact Submodule.finrank_orthogonal_span_singleton hu0
  let b := (stdOrthonormalBasis ℝ W).reindex (finCongr hdim)
  refine ⟨W.subtypeₗᵢ.comp b.repr.symm.toLinearIsometry,?_,?_⟩
  · intro x
    exact (Submodule.mem_orthogonal_singleton_iff_inner_right.mp (b.repr.symm x).property)
  · intro v hv
    have hvW : v ∈ W := Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hv
    refine ⟨b.repr ⟨v,hvW⟩,?_⟩
    change (b.repr.symm (b.repr ⟨v,hvW⟩)).val = v
    rw [LinearIsometryEquiv.symm_apply_apply]
end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Projectors_SimplexPoint
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine
open Set

lemma simplexInterior_isOpen (n : ℕ) : IsOpen (simplexInterior n) := by
  have h₁ : IsOpen {z : EuclideanSpace ℝ (Fin n) | ∀ i, 0 < z i} := by
    rw [show {z : EuclideanSpace ℝ (Fin n) | ∀ i, 0 < z i} =
      ⋂ i, {z : EuclideanSpace ℝ (Fin n) | 0 < z i} from by ext; simp]
    exact isOpen_iInter_of_finite (fun i => isOpen_lt continuous_const (EuclideanSpace.proj i).continuous)
  exact h₁.inter (isOpen_lt (continuous_finsetSum Finset.univ
    (fun i _ => (EuclideanSpace.proj i).continuous)) continuous_const)

lemma simplexInterior_nonempty (n : ℕ) : (simplexInterior n).Nonempty := by
  refine ⟨WithLp.toLp 2 (fun _ : Fin n => (1:ℝ)/(n+1)),?_,?_⟩
  · intro i
    change 0 < (1:ℝ)/(n+1)
    positivity
  · change ∑ _i : Fin n, (1:ℝ)/(n+1) < 1
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    rw [mul_one_div]
    exact (div_lt_one (by positivity)).mpr (by linarith)

lemma simplexPoint_pos {n : ℕ} {z : EuclideanSpace ℝ (Fin n)} (hz : z ∈ simplexInterior n) :
    ∀ i, 0 < simplexPoint z i := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact sub_pos.mpr hz.2
  · exact hz.1 j

lemma simplexPoint_sum {n : ℕ} (z : EuclideanSpace ℝ (Fin n)) : ∑ i, simplexPoint z i = 1 := by
  rw [Fin.sum_univ_succ]
  simp only [simplexPoint,Fin.cases_zero,Fin.cases_succ]
  ring

lemma simplexPoint_succ {n : ℕ} (z : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    simplexPoint z i.succ = z i := rfl
end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_SphereGeometry_TraceSphere
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator
section TraceSphere
variable {ν : Type*} [Fintype ν] [DecidableEq ν]
local notation "M" => Matrix ν ν ℝ

omit [DecidableEq ν] in
lemma matrix_trace_continuous : Continuous (Matrix.trace : M → ℝ) :=
  (Matrix.traceLinearMap ν ℝ ℝ).continuous_of_finiteDimensional

lemma traceSphere_ne_zero {A : M} (hA : A ∈ traceSphere ν) : A ≠ 0 := by
  intro h
  simpa [h] using hA.2

end TraceSphere
end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Support_PurityGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator
section PurityGeometry
variable {ν ι : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν] [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ ν

omit [DecidableEq ν] [Nonempty ν] [DecidableEq ι] in
lemma Admissible.orientedLevel_compact {f : E → ι → ℝ} (hf : Admissible f)
    (w : E) (r : ι → ℝ) : IsCompact (orientedLevel f w r) := by
  have hc : Continuous f := continuous_pi (fun i => (hf.smooth i).continuous)
  have he : orientedLevel f w r = Metric.sphere (0:E) 1 ∩
      {u | f u = r ∧ 0 ≤ ⟪w,u⟫} := by ext u; simp [orientedLevel]
  rw [he]
  exact (isCompact_sphere (0:E) 1).inter_right ((isClosed_eq hc continuous_const).inter
    (isClosed_le continuous_const (show Continuous (fun u : E => ⟪w,u⟫) from
      (continuous_const.inner continuous_id))))

omit [DecidableEq ν] [Nonempty ν] [DecidableEq ι] in
lemma Admissible.orientedLevel_inner_pos {f : E → ι → ℝ} (hf : Admissible f)
    {I : Finset ι} (hI : I.Nonempty) {w : E} (hw : ‖w‖ = 1)
    (hwi : ∀ i ∈ I, 0 < f w i) {r : ι → ℝ} (hr : ∀ i ∈ I, 0 < r i)
    {u : E} (hu : u ∈ orientedLevel f w r) : 0 < ⟪w,u⟫ := by
  apply lt_of_le_of_ne hu.2.2
  intro he
  obtain ⟨i,hi⟩ := hI
  exact hf.orthogonal w u hw hu.1 he.symm i ⟨hwi i hi,by rw [hu.2.1]; exact hr i hi⟩

end PurityGeometry
end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_LocalParity_RegularBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine
open Set
open scoped RealInnerProductSpace
section RegularBase
variable {k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ (Fin (k+1))
local notation "W" => EuclideanSpace ℝ (Fin k)

omit [DecidableEq ι] in
lemma Admissible.baseCoordinates_contDiff {f : E → ι → ℝ} (hf : Admissible f)
    {w : E} (hw : ‖w‖ = 1) (e : W →ₗᵢ[ℝ] E) (he : ∀ v, ⟪w,e v⟫ = 0)
    {I : Finset ι} (a : Fin (k+1) ≃ ↥I) : ContDiff ℝ (⊤ : ℕ∞) (baseCoordinates f w e a) := by
  apply (contDiff_piLp 2).mpr
  intro j
  exact (hf.smooth (a j.succ).val).comp (hemisphereChart_contDiff w e hw he)

omit [Fintype ι] in
lemma facetPoint_apply {I : Finset ι} (a : Fin (k+1) ≃ ↥I) (z : W) (j : Fin (k+1)) :
    facetPoint a z (a j).val = simplexPoint z j := by
  simp [facetPoint]

omit [Fintype ι] in
lemma facetPoint_pos {I : Finset ι} (a : Fin (k+1) ≃ ↥I) {z : W} (hz : z ∈ simplexInterior k) :
    ∀ i ∈ I, 0 < facetPoint a z i := by
  intro i hi
  simp only [facetPoint,dite_eq_left hi]
  exact simplexPoint_pos hz _

omit [Fintype ι] in
lemma facetPoint_zero {I : Finset ι} (a : Fin (k+1) ≃ ↥I) (z : W) {i : ι} (hi : i ∉ I) :
    facetPoint a z i = 0 := by simp [facetPoint,hi]

lemma facetPoint_sum {I : Finset ι} (a : Fin (k+1) ≃ ↥I) (z : W) : ∑ i, facetPoint a z i = 1 := by
  have h : ∑ i, facetPoint a z i = ∑ i : ↥I, simplexPoint z (a.symm i) := by
    calc
      _ = ∑ i ∈ I, facetPoint a z i := (Finset.sum_subset (Finset.subset_univ I)
        (fun i _ hi => facetPoint_zero a z hi)).symm
      _ = ∑ i : ↥I, facetPoint a z i.val := (Finset.sum_coe_sort I _).symm
      _ = _ := Finset.sum_congr rfl (fun i _ => by simp [facetPoint])
  rw [h,Equiv.sum_comp a.symm]
  exact simplexPoint_sum z

lemma Admissible.exists_regular_facet_point {f : E → ι → ℝ} (hf : Admissible f)
    {I : Finset ι} (a : Fin (k+1) ≃ ↥I) {w : E} (hw : ‖w‖ = 1)
    (hwi : ∀ i ∈ I, 0 < f w i) :
    ∃ (e : W →ₗᵢ[ℝ] E) (z : W), (∀ v, ⟪w,e v⟫ = 0) ∧
      (∀ u, ⟪w,u⟫ = 0 → ∃ v, e v = u) ∧ z ∈ simplexInterior k ∧
      (∀ v, baseCoordinates f w e a v = z → (fderiv ℝ (baseCoordinates f w e a) v).det ≠ 0) ∧
      (orientedLevel f w (facetPoint a z)).Finite := by
  obtain ⟨e,he,hes⟩ := orthogonal_frame k hw
  obtain ⟨z,hz,hr⟩ := exists_regular_value (baseCoordinates f w e a)
    ((hf.baseCoordinates_contDiff hw e he a).differentiable (by simp)) (simplexInterior_isOpen k) (simplexInterior_nonempty k)
  refine ⟨e,z,he,hes,hz,hr,?_⟩
  let K := orientedLevel f w (facetPoint a z)
  have hI : I.Nonempty := ⟨(a 0).val,(a 0).property⟩
  have hp : K ⊆ {u | 0 < ⟪w,u⟫} := fun u hu =>
    hf.orientedLevel_inner_pos hI hw hwi (facetPoint_pos a hz) hu
  have hcont : ContinuousOn (hemisphereInverse w e) K := (hemisphereInverse_continuousOn w e).mono hp
  have hc := (hf.orientedLevel_compact w (facetPoint a z)).image_of_continuousOn hcont
  have hK : ∀ v ∈ hemisphereInverse w e '' K, baseCoordinates f w e a v = z := by
    rintro v ⟨u,hu,rfl⟩
    ext j
    change f (hemisphereChart w e (hemisphereInverse w e u)) (a j.succ).val = z j
    rw [hemisphereChart_inverse w e hw he hes hu.1 (hp hu),hu.2.1,facetPoint_apply,simplexPoint_succ]
  have hfin := compact_regular_level_finite (baseCoordinates f w e a)
    ((hf.baseCoordinates_contDiff hw e he a).of_le (by simp)) hc hK hr
  apply (Set.finite_image_iff ?_).mp hfin
  intro u hu v hv huv
  have hh := congrArg (hemisphereChart w e) huv
  rwa [hemisphereChart_inverse w e hw he hes hu.1 (hp hu),
    hemisphereChart_inverse w e hw he hes hv.1 (hp hv)] at hh
end RegularBase
end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_MatrixGeometry_BlockParts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine
open scoped MatrixOrder RealInnerProductSpace Matrix.Norms.L2Operator
section BlockParts
variable {μ ν ι : Type*} [Fintype μ] [Fintype ν] [DecidableEq μ] [DecidableEq ν]
  [Nonempty ν] [Fintype ι]
local notation "W" => EuclideanSpace ℝ μ
local notation "E" => EuclideanSpace ℝ ν
local notation "M" => Matrix ν ν ℝ
local notation "op" => Matrix.toEuclideanCLM (𝕜 := ℝ)

omit [Nonempty ν] in
lemma matrixCompress_rankOne (e : W →ₗᵢ[ℝ] E) {c : E} (he : ∀ v, ⟪c,e v⟫ = 0) :
    matrixCompress e (rankOne c) = 0 := by
  apply (Matrix.toEuclideanCLM (n := μ) (𝕜 := ℝ)).injective
  apply ContinuousLinearMap.ext
  intro v
  change op (matrixCompress e (rankOne c)) v = op (0 : Matrix μ μ ℝ) v
  rw [matrixCompress_action,rankOne_action,he,zero_smul,map_zero,map_zero,
    zero_apply]

omit [Nonempty ν] in
lemma block_decomposition {c : E} (e : W →ₗᵢ[ℝ] E) (hc : ‖c‖ = 1)
    (he : ∀ v, ⟪c,e v⟫ = 0) (hes : ∀ u, ⟪c,u⟫ = 0 → ∃ v, e v = u)
    {A : M} (hA : IsSelfAdjoint A) (hb : blockOff c e A = 0) :
    A = blockScalar c A • rankOne c + blockCorner e A := by
  have hAc : op A c = blockScalar c A • c := by
    have hd := frame_decomposition c e hc he hes (op A c)
    change e (blockOff c e A) = op A c - blockScalar c A • c at hd
    rw [hb,map_zero] at hd
    exact sub_eq_zero.mp hd.symm
  have hP := (rankOne_nonneg c).isSelfAdjoint
  have hB : IsSelfAdjoint (A - blockScalar c A • rankOne c) := hA.sub ((IsSelfAdjoint.all _).smul hP)
  have hk : op (A - blockScalar c A • rankOne c) c = 0 := by
    rw [map_sub,sub_apply,map_smul,smul_apply,
      rankOne_action,real_inner_self_eq_norm_sq,hc,one_pow,one_smul,hAc,sub_self]
  have hh := blockCorner_of_kernel e hes hB hk
  have hC : blockCorner e (A - blockScalar c A • rankOne c) = blockCorner e A := by
    simp only [blockCorner,map_sub,map_smul,matrixCompress_rankOne e he,smul_zero,sub_zero]
  rw [hC] at hh
  rw [hh]
  abel

end BlockParts
end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_MatrixGeometry_LineRepresentative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator Topology
section LineRepresentative
variable {ν : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν]
local notation "E" => EuclideanSpace ℝ ν
local notation "M" => Matrix ν ν ℝ
local notation "op" => Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)

omit [Fintype ν] [DecidableEq ν] [Nonempty ν] in
lemma rankOne_smul (t : ℝ) (u : E) : rankOne (t • u) = t^2 • rankOne u := by
  ext i j
  simp only [rankOne,PiLp.smul_apply,Matrix.smul_apply,smul_eq_mul]
  ring

omit [DecidableEq ν] [Nonempty ν] in
lemma rankOne_unit_span {u v : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hsp : v ∈ Submodule.span ℝ {u}) : rankOne v = rankOne u := by
  obtain ⟨t,ht⟩ := Submodule.mem_span_singleton.mp hsp
  change t • u = v at ht
  have hn : |t| = 1 := by simpa only [← ht,norm_smul,Real.norm_eq_abs,hu,mul_one] using hv
  have hs : t^2 = 1 := by nlinarith [sq_abs t]
  rw [← ht,rankOne_smul,hs,one_smul]

omit [Nonempty ν] in
lemma lineRepresentative_norm {w : E} {A : M} (hAw : op A⁺ w ≠ 0) :
    ‖lineRepresentative w A‖ = 1 := by
  simp [lineRepresentative,norm_smul,norm_inv,hAw]

omit [Nonempty ν] in
lemma hasPositiveLine_trace_pos {A : M} (hA : HasPositiveLine A) :
    0 < Matrix.trace A⁺ := by
  obtain ⟨u,hu,lam,hl,he⟩ := hA
  rwa [he,Matrix.trace_smul,rankOne_trace,hu,one_pow,smul_eq_mul,mul_one]

omit [Nonempty ν] in
lemma positive_line_representative {w : E} {A : M} (hA : HasPositiveLine A)
    (hAw : op A⁺ w ≠ 0) : A⁺ = Matrix.trace A⁺ • rankOne (lineRepresentative w A) := by
  obtain ⟨u,hu,lam,hl,he⟩ := hA
  have hsp : lineRepresentative w A ∈ Submodule.span ℝ {u} := by
    rw [lineRepresentative,he,map_smul,smul_apply,rankOne_action]
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _
      (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton u))))
  have hp := rankOne_unit_span hu (lineRepresentative_norm hAw) hsp
  rw [hp,he,Matrix.trace_smul,rankOne_trace,hu,one_pow,smul_eq_mul,mul_one]

end LineRepresentative
end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Support_NegativeFibre
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator
section NegativeFibre
variable {ν : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν]
local notation "E" => EuclideanSpace ℝ ν
local notation "M" => Matrix ν ν ℝ
local notation "op" => Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)

lemma negPart_kernel_of_positiveLine {A : M} {u : E} (hu : ‖u‖ = 1)
    {lam : ℝ} (hl : 0 < lam) (he : A⁺ = lam • rankOne u) : op A⁻ u = 0 := by
  have hz : op A⁻ (op A⁺ u) = 0 := by
    have h := congrArg (fun B : M => op B u) (CFC.negPart_mul_posPart A)
    simpa only [map_mul,map_zero,mul_apply_eq_comp,zero_apply] using h
  rw [he,map_smul,smul_apply,rankOne_action,real_inner_self_eq_norm_sq,
    hu,one_pow,one_smul,map_smul] at hz
  exact (smul_eq_zero.mp hz).resolve_left (ne_of_gt hl)

end NegativeFibre
end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_MatrixGeometry_BlockLine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine
open scoped Matrix MatrixOrder RealInnerProductSpace Matrix.Norms.L2Operator
section BlockLine
variable {μ ν : Type*} [Fintype μ] [Fintype ν] [DecidableEq μ] [DecidableEq ν]
  [Nonempty ν]
local notation "W" => EuclideanSpace ℝ μ
local notation "E" => EuclideanSpace ℝ ν
local notation "M" => Matrix ν ν ℝ
local notation "op" => Matrix.toEuclideanCLM (𝕜 := ℝ)
lemma positiveLine_eigenvector {A : M} (hA : IsSelfAdjoint A) {c : E} (hc : ‖c‖ = 1)
    {lam : ℝ} (hl : 0 < lam) (hP : A⁺ = lam • rankOne c) : op A c = lam • c := by
  rw [← CFC.posPart_sub_negPart A hA,map_sub,sub_apply,
    negPart_kernel_of_positiveLine hc hl hP,sub_zero,hP,map_smul,smul_apply,
    rankOne_action,real_inner_self_eq_norm_sq,hc,one_pow,one_smul]
lemma blockScalar_positiveLine {A : M} (hA : IsSelfAdjoint A) {c : E} (hc : ‖c‖ = 1)
    {lam : ℝ} (hl : 0 < lam) (hP : A⁺ = lam • rankOne c) : blockScalar c A = lam := by
  rw [blockScalar,positiveLine_eigenvector hA hc hl hP,inner_smul_right,real_inner_self_eq_norm_sq,hc,one_pow,mul_one]
omit [DecidableEq μ] in
lemma blockOff_positiveLine (e : W →ₗᵢ[ℝ] E) {A : M} (hA : IsSelfAdjoint A) {c : E} (hc : ‖c‖ = 1)
    (he : ∀ v, ⟪c,e v⟫ = 0) {lam : ℝ} (hl : 0 < lam) (hP : A⁺ = lam • rankOne c) :
    blockOff c e A = 0 := by
  rw [blockOff,positiveLine_eigenvector hA hc hl hP,map_smul,adjoint_normal c e he,smul_zero]
lemma blockCorner_positiveLine (e : W →ₗᵢ[ℝ] E) {A : M} (hA : IsSelfAdjoint A) {c : E} (hc : ‖c‖ = 1)
    (he : ∀ v, ⟪c,e v⟫ = 0) (hes : ∀ u, ⟪c,u⟫ = 0 → ∃ v, e v = u)
    {lam : ℝ} (hl : 0 < lam) (hP : A⁺ = lam • rankOne c) : blockCorner e A = -A⁻ := by
  have hd := block_decomposition e hc he hes hA (blockOff_positiveLine e hA hc he hl hP)
  rw [blockScalar_positiveLine hA hc hl hP] at hd
  have hp := CFC.posPart_sub_negPart A hA
  rw [hP] at hp
  exact (add_left_cancel (show lam • rankOne c + -A⁻ = lam • rankOne c + blockCorner e A by simpa only [sub_eq_add_neg] using hp.trans hd)).symm

omit [Nonempty ν] in
lemma blockCompress_isUnit (e : W →ₗᵢ[ℝ] E) {A : M} (hA : IsSelfAdjoint A) (hU : IsUnit A)
    {c : E} (hc : ‖c‖ = 1) (he : ∀ v, ⟪c,e v⟫ = 0)
    (hes : ∀ u, ⟪c,u⟫ = 0 → ∃ v, e v = u) (hb : blockOff c e A = 0) :
    IsUnit (matrixCompress e A) := by
  have hopU : IsUnit (op A) := IsUnit.map (Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)) hU
  have hAi : Function.Injective (op A) := (ContinuousLinearMap.isUnit_iff_bijective.mp hopU).1
  apply (isUnit_map_iff (op) _).mp
  apply ContinuousLinearMap.isUnit_iff_bijective.mpr
  have hi : Function.Injective (op (matrixCompress e A)) := by
    apply (LinearMap.ker_eq_bot).mp
    rw [Submodule.eq_bot_iff]
    intro v hv
    have hv0 : op (matrixCompress e A) v = 0 := hv
    have hAv : op A (e v) = 0 := by
      conv_lhs => rw [block_decomposition e hc he hes hA hb]
      rw [map_add,add_apply,map_smul,smul_apply,
        rankOne_action,he,zero_smul,smul_zero,zero_add]
      change op (matrixEmbed e (matrixCompress e A)) (e v) = 0
      rw [show op (matrixEmbed e (matrixCompress e A)) (e v) = e (op (matrixCompress e A) v) from matrixEmbed_action e _ v,hv0,map_zero]
    apply e.injective
    exact hAi (by simpa only [map_zero] using hAv)
  exact ⟨hi,(LinearMap.injective_iff_surjective).mp hi⟩

lemma posDef_inner_pos {B : Matrix μ μ ℝ} (hB : B.PosDef) {v : W} (hv : v ≠ 0) :
    0 < ⟪v,op B v⟫ := by
  have hv' : v.ofLp ≠ 0 := fun h => hv (WithLp.ofLp_injective 2 h)
  have h := hB.dotProduct_mulVec_pos hv'
  simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial]
  change 0 < ∑ i, (B *ᵥ v.ofLp) i * v i
  simpa only [dotProduct,Pi.star_apply,star_trivial,mul_comm] using h

lemma blockCompress_negative (e : W →ₗᵢ[ℝ] E) {A : M} (hA : IsSelfAdjoint A) (hU : IsUnit A)
    {c : E} (hc : ‖c‖ = 1) (he : ∀ v, ⟪c,e v⟫ = 0)
    (hes : ∀ u, ⟪c,u⟫ = 0 → ∃ v, e v = u) {lam : ℝ} (hl : 0 < lam)
    (hP : A⁺ = lam • rankOne c) : NegativeQuadratic (op (matrixCompress e A)) := by
  have hC := blockCorner_positiveLine e hA hc he hes hl hP
  have hcomp : -(matrixCompress e A) = matrixCompress e A⁻ := by
    have hh := congrArg (matrixCompress e) hC
    rw [blockCorner,matrixCompress_embed,map_neg] at hh
    exact neg_eq_iff_eq_neg.mpr hh
  have hn : 0 ≤ -(matrixCompress e A) := by rw [hcomp]; exact matrixCompress_nonneg e (CFC.negPart_nonneg A)
  have hunit := (blockCompress_isUnit e hA hU hc he hes (blockOff_positiveLine e hA hc he hl hP)).neg
  have hpd := (Matrix.nonneg_iff_posSemidef.mp hn).posDef_iff_isUnit.mpr hunit
  intro v hv
  have h := posDef_inner_pos hpd hv
  rw [map_neg,neg_apply,inner_neg_right] at h
  exact neg_pos.mp h
end BlockLine
end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_LocalParity_RegularModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine
open scoped RealInnerProductSpace
section RegularModel
variable {k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ (Fin (k+1))
local notation "W" => EuclideanSpace ℝ (Fin k)
lemma Admissible.regular_model_data {f : E → ι → ℝ} (hf : Admissible f)
    {I : Finset ι} (a : Fin (k+1) ≃ ↥I) {w c : E} (hw : ‖w‖ = 1) (hc : ‖c‖ = 1)
    (e : W →ₗᵢ[ℝ] E) (he : ∀ v, ⟪w,e v⟫ = 0) (hes : ∀ u, ⟪w,u⟫ = 0 → ∃ v, e v = u)
    (hwc : 0 < ⟪w,c⟫) {z : W} (hcval : f c = facetPoint a z)
    (hr : ∀ v, baseCoordinates f w e a v = z → (fderiv ℝ (baseCoordinates f w e a) v).det ≠ 0) :
    ∃ (d : W →ₗᵢ[ℝ] E) (D : W ≃L[ℝ] W) (δ : ℝ),
      (∀ v, ⟪c,d v⟫ = 0) ∧ (∀ u, ⟪c,u⟫ = 0 → ∃ v, d v = u) ∧ 0 < δ ∧
      ∀ u : E, ‖u‖ = 1 → 0 < ⟪c,u⟫ → ‖hemisphereInverse c d u‖ < δ →
        hemisphereInverse c d u ≠ 0 → 0 < ⟪hemisphereInverse c d u,D.symm (facetTail a (f u-f c))⟫ := by
  obtain ⟨d,hd,hds⟩ := orthogonal_frame k hc
  let F : E → W := fun u => facetTail a (f u)
  have hF : ContDiff ℝ (⊤ : ℕ∞) F := by
    apply (contDiff_piLp 2).mpr
    intro j
    exact hf.smooth (a j.succ).val
  have hz : baseCoordinates f w e a (hemisphereInverse w e c) = z := by
    ext j
    change f (hemisphereChart w e (hemisphereInverse w e c)) (a j.succ).val = z j
    rw [hemisphereChart_inverse w e hw he hes hc hwc,hcval,facetPoint_apply,simplexPoint_succ]
  have hdet : (fderiv ℝ (baseCoordinates f c d a) 0).det ≠ 0 :=
    hemisphere_transition_regular hw hc e d he hd hes hds hwc F hF (hr _ hz)
  let D : W ≃L[ℝ] W :=
    (fderiv ℝ (baseCoordinates f c d a) 0).toContinuousLinearEquivOfDetNeZero hdet
  have hD : D.toContinuousLinearMap = fderiv ℝ (baseCoordinates f c d a) 0 := by
    exact ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero _ hdet
  let g : W → W := fun v => baseCoordinates f c d a v - F c
  have hg0 : g 0 = 0 := by
    change F (hemisphereChart c d 0) - F c = 0
    rw [hemisphereChart_zero hc,sub_self]
  have hgd : HasFDerivAt g D.toContinuousLinearMap 0 := by
    rw [hD]
    exact (((hf.baseCoordinates_contDiff hc d hd a).differentiable (by simp) 0).hasFDerivAt).sub_const (F c)
  obtain ⟨δ,hδ,hpos⟩ := regular_inner_positive D hg0 hgd
  refine ⟨d,D,δ,hd,hds,hδ,?_⟩
  intro u hu hcu hδu hv
  have hg : g (hemisphereInverse c d u) = facetTail a (f u-f c) := by
    change F (hemisphereChart c d (hemisphereInverse c d u)) - F c = _
    rw [hemisphereChart_inverse c d hc hd hds hu hcu]
    exact (map_sub (facetTail a) _ _).symm
  rw [← hg]
  exact hpos _ hδu hv
end RegularModel
end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Projectors_CoordinateSum
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped BigOperators

lemma coordinateSum_apply {ι : Type*} [Fintype ι] (x : EuclideanSpace ℝ ι) :
    coordinateSum x = ∑ i, x i := rfl

lemma coordinateSum_uniform (ι : Type*) [Fintype ι] [Nonempty ι] :
    coordinateSum (uniformVector ι) = 1 := by
  simp only [coordinateSum_apply,uniformVector,Finset.sum_const,
    Finset.card_univ,nsmul_eq_mul]
  exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (ne_of_gt (Fintype.card_pos)))

end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Support_BalancedChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
section BalancedChart
variable {ν : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν]
local notation "E" => EuclideanSpace ℝ ν
local notation "M" => Matrix ν ν ℝ
local notation "op" => Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)

omit [Nonempty ν] in
lemma lineRepresentative_split {u w : E} (hu : ‖u‖ = 1) {A : M} {lam : ℝ}
    (hl : 0 < lam) (he : A⁺ = lam • rankOne u) (hwu : 0 < ⟪w,u⟫) :
    lineRepresentative w A = u := by
  have hp : 0 < lam * ⟪u,w⟫ := mul_pos hl (by simpa only [real_inner_comm] using hwu)
  have hop : op A⁺ w = (lam * ⟪u,w⟫) • u := by
    rw [he,map_smul,smul_apply,rankOne_action,smul_smul]
  rw [lineRepresentative,hop,norm_smul,Real.norm_eq_abs,abs_of_pos hp,hu,mul_one,smul_smul,inv_mul_cancel₀ (ne_of_gt hp),one_smul]

end BalancedChart
end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Projectors_RaySet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine
lemma raySet_isClosed {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (y : E) :
    IsClosed (raySet y) := isClosed_eq continuous_id ((continuous_norm.div_const _).smul continuous_const)
lemma mem_raySet_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {v y : E} (hv : v ≠ 0) (hy : y ≠ 0) : v ∈ raySet y ↔ ∃ d : ℝ, 0 < d ∧ v = d • y := by
  constructor
  · intro h
    exact ⟨‖v‖ / ‖y‖,div_pos (norm_pos_iff.mpr hv) (norm_pos_iff.mpr hy),h⟩
  · rintro ⟨d,hd,rfl⟩
    change d • y = (‖d • y‖ / ‖y‖) • y
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hd,mul_div_cancel_right₀ _ (norm_ne_zero_iff.mpr hy)]
end BorsukNine

namespace BorsukNine
open Set
open scoped MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
section MatrixFibres
variable {k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ (Fin (k+1))
local notation "W" => EuclideanSpace ℝ (Fin k)
local notation "T" => traceSphere (Fin (k+1))
local notation "Y" => EuclideanSpace ℝ ι
local notation "op" => Matrix.toEuclideanCLM (n := Fin (k+1)) (𝕜 := ℝ)
omit [DecidableEq ι] in
lemma matrixRayFibre_closed (F : T → Y) (hF : Continuous F) (y : Y) (c : E) :
    IsClosed (matrixRayFibre F y c) := by
  have hp : Continuous (fun A : T => A.val⁺) :=
    matrix_posPart_continuousOn.comp_continuous continuous_subtype_val (fun A => A.property.1)
  exact ((raySet_isClosed y).preimage hF).inter
    (isClosed_eq hp ((matrix_trace_continuous.comp hp).smul continuous_const))
lemma Admissible.facet_support {f : E → ι → ℝ} (_hf : Admissible f)
    {I : Finset ι} (a : Fin (k+1) ≃ ↥I) {z : W} (hz : z ∈ simplexInterior k)
    {c : E} (hc : f c = facetPoint a z) : positiveSupport f c = I := by
  ext i
  rw [mem_positiveSupport,hc]
  by_cases hi : i ∈ I
  · exact iff_of_true (facetPoint_pos a hz i hi) hi
  · rw [facetPoint_zero a z hi]
    simp [hi]
omit [DecidableEq ι] in
lemma matrixRayFibre_representative {F : T → Y} {y : Y} {w c : E} (hc : ‖c‖ = 1)
    (hwc : 0 < ⟪w,c⟫) {A : T} (hline : HasPositiveLine A.val)
    (hK : A ∈ matrixRayFibre F y c) : lineRepresentative w A.val = c :=
  lineRepresentative_split hc (hasPositiveLine_trace_pos hline) hK.2 hwc
omit [DecidableEq ι] in
lemma Admissible.matrixRayFibre_subset_patch {f : E → ι → ℝ} (_hf : Admissible f)
    {F : T → Y} {y : Y} {w c : E} (hc : ‖c‖ = 1) (hwc : 0 < ⟪w,c⟫)
    {I : Finset ι} (hp : ∀ i ∈ I, 0 < f c i)
    (e : W →ₗᵢ[ℝ] E) (he : ∀ v, ⟪c,e v⟫ = 0)
    (hes : ∀ u, ⟪c,u⟫ = 0 → ∃ v, e v = u) {δ : ℝ} (hδ : 0 < δ)
    {A : T} (hK : A ∈ matrixRayFibre F y c)
    (hU : IsUnit A.val) (hline : HasPositiveLine A.val) (hAw : op A.val⁺ w ≠ 0) :
    A ∈ regularPatch f I w c e δ := by
  have hr := matrixRayFibre_representative hc hwc hline hK
  have ht := hasPositiveLine_trace_pos hline
  refine ⟨hU,hline,hAw,?_,?_,?_,?_,?_⟩
  · simpa only [hr] using hp
  · rw [hr,real_inner_self_eq_norm_sq,hc]; norm_num
  · rw [hr,hemisphereInverse,adjoint_normal c e he,smul_zero,norm_zero]
    exact hδ
  · rw [blockScalar_positiveLine A.property.1 hc ht hK.2]
    exact ht
  · exact blockCompress_negative e A.property.1 hU hc he hes ht hK.2
end MatrixFibres
end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_MatrixGeometry_BlockVector
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped BigOperators
section BlockVector
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma blockVector_in (I : Finset ι) (lam : ℝ) (r : ι → ℝ) (mu : ℝ)
    (z : EuclideanSpace ℝ ↥(Iᶜ : Finset ι)) {i : ι} (hi : i ∈ I) :
    blockVector I lam r mu z i = lam * r i := by simp [blockVector,hi]
lemma blockVector_out (I : Finset ι) (lam : ℝ) (r : ι → ℝ) (mu : ℝ)
    (z : EuclideanSpace ℝ ↥(Iᶜ : Finset ι)) (i : ↥(Iᶜ : Finset ι)) :
    blockVector I lam r mu z i.val = -mu * z i := by simp [blockVector,Finset.mem_compl.mp i.property]

lemma blockVector_nonzero {I : Finset ι} (hI : I.Nonempty) {lam mu : ℝ} (hl : 0 < lam)
    {r : ι → ℝ} (hr : ∀ i ∈ I, 0 < r i) (z : EuclideanSpace ℝ ↥(Iᶜ : Finset ι)) :
    blockVector I lam r mu z ≠ 0 := by
  obtain ⟨i,hi⟩ := hI
  intro h
  have he := congrArg (fun v : EuclideanSpace ℝ ι => v i) h
  rw [blockVector_in _ _ _ _ _ hi] at he
  exact (ne_of_gt (mul_pos hl (hr i hi))) he

end BlockVector
end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_LocalParity_MatrixParity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine
open Set SimplicialChains
open scoped MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
section MatrixParity
variable {k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ (Fin (k+1))
local notation "W" => EuclideanSpace ℝ (Fin k)
local notation "T" => traceSphere (Fin (k+1))
local notation "Y" => EuclideanSpace ℝ ι
lemma Admissible.regular_facet_level_odd {f : E → ι → ℝ} (hf : Admissible f)
    (hdim : Fintype.card (UpperTriangle (Fin (k+1))) = Fintype.card ι)
    (hn : 1 < Fintype.card ι) {I : Finset ι} [Nonempty ↥(Iᶜ : Finset ι)]
    (a : Fin (k+1) ≃ ↥I)
    (hmax : ∀ u : E, ‖u‖ = 1 → I ⊆ positiveSupport f u → positiveSupport f u = I)
    {w : E} (hw : ‖w‖ = 1) (hwi : ∀ i ∈ I, 0 < f w i)
    (e : W →ₗᵢ[ℝ] E) (he : ∀ v, ⟪w,e v⟫ = 0)
    (hes : ∀ u, ⟪w,u⟫ = 0 → ∃ v, e v = u) {z : W} (hz : z ∈ simplexInterior k)
    (hr : ∀ v, baseCoordinates f w e a v = z → (fderiv ℝ (baseCoordinates f w e a) v).det ≠ 0)
    (hfin : (orientedLevel f w (facetPoint a z)).Finite) :
    (Nat.card (orientedLevel f w (facetPoint a z)) : F₂) = 1 := by
  classical
  let L := orientedLevel f w (facetPoint a z)
  let : Fintype L := hfin.fintype
  have hI : I.Nonempty := ⟨(a 0).val,(a 0).property⟩
  have hc (c : L) : ‖c.val‖ = 1 := c.property.1
  have hcv (c : L) : f c.val = facetPoint a z := c.property.2.1
  have hcw (c : L) : 0 < ⟪w,c.val⟫ := hf.orientedLevel_inner_pos hI hw hwi (facetPoint_pos a hz) c.property
  have hcp (c : L) : positiveSupport f c.val = I := hf.facet_support a hz (hcv c)
  have hdata (c : L) := hf.regular_model_data a hw (hc c) e he hes (hcw c) (hcv c) hr
  choose d D δ hd hds hδ hreg using hdata
  let v := uniformVector ↥(Iᶜ : Finset ι)
  have hv (i : ↥(Iᶜ : Finset ι)) : 0 < v i := by
    change 0 < (Fintype.card ↥(Iᶜ : Finset ι) : ℝ)⁻¹
    positivity
  have hvs : ∑ i, v i = 1 := coordinateSum_uniform _
  let y : Y := blockVector I (1/2:ℝ) (facetPoint a z) (1/2:ℝ) v
  have hy : y ≠ 0 := blockVector_nonzero hI (by norm_num) (facetPoint_pos a hz) _
  let F : T → Y := fun A => WithLp.toLp 2 (signedExtension f A.val)
  let G : L → T → Y := fun c A => WithLp.toLp 2 (localBlockModel f c.val (d c) a (D c) A.val)
  let K : L → Set T := fun c => matrixRayFibre F y c.val
  let S : L → Set T := fun c => regularPatch f I w c.val (d c) (δ c)
  have hF : Continuous F := (PiLp.continuous_toLp 2 _).comp
    (hf.signedExtension_continuousOn.comp_continuous continuous_subtype_val (fun A => A.property.1))
  have hFz (A : T) : F A ≠ 0 := by
    intro hzA
    exact traceSphere_ne_zero A.property ((hf.signedExtension_eq_zero_iff A.property.1).mp (WithLp.toLp_injective 2 hzA))
  have hFroot (A : T) (hA : F A ∈ raySet y) :
      IsUnit A.val ∧ HasPositiveLine A.val ∧
      (Matrix.toEuclideanCLM (n := Fin (k+1)) (𝕜 := ℝ) A.val⁺) w ≠ 0 ∧
      0 < Matrix.trace A.val⁻ ∧ lineRepresentative w A.val ∈ L := by
    obtain ⟨t,ht,hAt⟩ := (mem_raySet_iff (hFz A) hy).mp hA
    exact hf.original_ray_level hI hmax hw hwi (facetPoint_pos a hz) (fun i hi => facetPoint_zero a z hi)
      (facetPoint_sum a z) hv hvs A.property ht hAt
  have hG (c : L) : Continuous (G c) := (PiLp.continuous_toLp 2 _).comp
    ((hf.localBlockModel_continuousOn c.val (d c) a (D c)).comp_continuous continuous_subtype_val
      (fun A => A.property.1))
  have hGz (c : L) (A : T) : G c A ≠ 0 := by
    intro hzA
    exact hf.localBlockModel_ne_zero (hc c) (d c) (hd c) (hds c) a (hcp c) (D c)
      A.property.1 (traceSphere_ne_zero A.property) (WithLp.toLp_injective 2 hzA)
  have hKS (c : L) : K c ⊆ S c := by
    intro A hA
    have hh := hFroot A hA.1
    exact hf.matrixRayFibre_subset_patch (hc c) (hcw c) (by simpa only [hcv c] using facetPoint_pos a hz)
      (d c) (hd c) (hds c) (hδ c) hA hh.1 hh.2.1 hh.2.2.1
  have hKd : Pairwise (fun c c' => Disjoint (K c) (K c')) := by
    intro c c' hcc
    apply Set.disjoint_left.mpr
    intro A hA hA'
    have hh := hFroot A hA.1
    apply hcc
    apply Subtype.ext
    exact (matrixRayFibre_representative (hc c) (hcw c) hh.2.1 hA).symm.trans
      (matrixRayFibre_representative (hc c') (hcw c') hh.2.1 hA')
  have hyi (c : L) (i : ι) (hi : i ∈ I) : y i = (1/2:ℝ)*f c.val i := by
    rw [hcv c]
    exact blockVector_in I _ _ _ _ hi
  have hyo (i : ι) (hi : i ∉ I) : y i ≤ 0 := by
    have hh := blockVector_out I (1/2:ℝ) (facetPoint a z) (1/2:ℝ) v ⟨i,Finset.mem_compl.mpr hi⟩
    change y i = _ at hh
    rw [hh]
    exact mul_nonpos_of_nonpos_of_nonneg (by norm_num) (hv _).le
  have hcover (A : T) (hA : ∃ t : ℝ, 0 < t ∧ F A = t • y) : ∃ c, A ∈ K c := by
    have hray := (mem_raySet_iff (hFz A) hy).mpr hA
    have hh := hFroot A hray
    exact ⟨⟨lineRepresentative w A.val,hh.2.2.2.2⟩,hray,positive_line_representative hh.2.1 hh.2.2.1⟩
  have hroot (c : L) (A : T) (hA : ∃ t : ℝ, 0 < t ∧ G c A = t • y) : A ∈ K c := by
    obtain ⟨t,ht,hAt⟩ := hA
    have hm : localBlockModel f c.val (d c) a (D c) A.val = t • y.ofLp := WithLp.toLp_injective 2 hAt
    obtain ⟨hb,ha,heq,hP⟩ := hf.localBlockModel_ray (hc c) (d c) (hd c) (hds c) a (hcp c) (D c)
      A.property.1 (by norm_num : (0:ℝ) < 1/2) ht (hyi c) hyo hm
    have hFt : F A = t • y := by simpa only [F,G,heq] using hAt
    refine ⟨(mem_raySet_iff (hFz A) hy).mpr ⟨t,ht,hFt⟩,?_⟩
    have htr : Matrix.trace A.val⁺ = blockScalar c.val A.val := by
      rw [hP,Matrix.trace_smul,rankOne_trace,hc c,one_pow,smul_eq_mul,mul_one]
    rwa [htr]
  have hseg (c : L) (A : T) (hA : A ∈ S c) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      (1-t) • F A + t • G c A ≠ 0 := by
    have hnU := lineRepresentative_norm hA.2.2.1
    have hIU : positiveSupport f (lineRepresentative w A.val) = I := hmax _ hnU
      (fun i hi => (mem_positiveSupport f _ i).mpr (hA.2.2.2.1 i hi))
    have hh := hf.localBlockMix_ne_zero A.property.1 (hc c) hnU (d c) (hd c) a (hcp c) hIU (D c)
      (hasPositiveLine_trace_pos hA.2.1) (positive_line_representative hA.2.1 hA.2.2.1) hA.2.2.2.2.2.2.1 ht
    intro hzA
    exact hh (WithLp.toLp_injective 2 hzA)
  have hhit (c : L) (A : T) (hA : A ∈ S c) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1)
      (hAt : ∃ b : ℝ, 0 < b ∧ (1-t) • F A + t • G c A = b • y) : A ∈ K c := by
    obtain ⟨b,hb,heq⟩ := hAt
    have hnU := lineRepresentative_norm hA.2.2.1
    have hIU : positiveSupport f (lineRepresentative w A.val) = I := hmax _ hnU
      (fun i hi => (mem_positiveSupport f _ i).mpr (hA.2.2.2.1 i hi))
    have hmix : localBlockMix f c.val (d c) a (D c) t A.val = b • y.ofLp := WithLp.toLp_injective 2 heq
    obtain ⟨huc,hme⟩ := hf.localBlockMix_hit A.property.1 (hc c) hnU (d c) (hd c) (hds c) a (hcp c) hIU (D c)
      (hasPositiveLine_trace_pos hA.2.1) (positive_line_representative hA.2.1 hA.2.2.1)
      hA.2.2.2.2.1 hA.2.2.2.2.2.2.2
      (hreg c _ hnU hA.2.2.2.2.1 hA.2.2.2.2.2.1) (hyi c) ht hmix
    refine ⟨(mem_raySet_iff (hFz A) hy).mpr ⟨b,hb,?_⟩,?_⟩
    · exact congrArg (WithLp.toLp 2) (hme.symm.trans hmix)
    · rw [← huc]
      exact positive_line_representative hA.2.1 hA.2.2.1
  have hp := trace_patch_models hdim hn F hF hFz (by
      intro A B hB
      simp only [F,hB,signedExtension_odd,WithLp.toLp_neg])
    G hG hGz (by
      intro c A B hB
      simp only [G,hB,localBlockModel_odd,WithLp.toLp_neg])
    K S (fun c => matrixRayFibre_closed F hF y c.val) (fun c => hf.regularPatch_isOpen I w c.val (d c) (δ c))
    hKS hKd hy hcover hroot hseg hhit
  simpa only [Nat.card_eq_fintype_card] using hp
end MatrixParity
end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_LocalParity_NoFreeRidge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine
open Set SimplicialChains
open scoped RealInnerProductSpace
section NoFreeRidge
variable {k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ (Fin (k+1))
lemma Admissible.no_free_indexed_facet {f : E → ι → ℝ} (hf : Admissible f)
    (hk : 0 < k) (hdim : Fintype.card (UpperTriangle (Fin (k+1))) = Fintype.card ι)
    (hn : 1 < Fintype.card ι) {I : Finset ι} [Nonempty ↥(Iᶜ : Finset ι)]
    (a : Fin (k+1) ≃ ↥I)
    (hmax : ∀ u : E, ‖u‖ = 1 → I ⊆ positiveSupport f u → positiveSupport f u = I)
    {w : E} (hw : ‖w‖ = 1) (hwi : ∀ i ∈ I, 0 < f w i) :
    ∃ u : E, ‖u‖ = 1 ∧ (∀ j : Fin k, 0 < f u (a j.succ).val) ∧ ¬ positiveSupport f u ⊆ I := by
  classical
  by_contra hnfree
  push Not at hnfree
  obtain ⟨e,z,he,hes,hz,hr,hfin⟩ := hf.exists_regular_facet_point a hw hwi
  have ho := hf.regular_facet_level_odd hdim hn a hmax hw hwi e he hes hz hr hfin
  have heven := hf.regular_facet_level_even hk a hnfree hw hwi e he hes hz hr hfin
  rw [heven] at ho
  exact zero_ne_one ho

lemma Admissible.no_free_ridge_oai {f : E → ι → ℝ} (hf : Admissible f)
    (hk : 0 < k) (hdim : Fintype.card (UpperTriangle (Fin (k+1))) = Fintype.card ι)
    (hn : 1 < Fintype.card ι) {I U : Finset ι} [Nonempty ↥(Iᶜ : Finset ι)]
    (hI : I.card = k+1) (hUI : U ⊆ I) (hU : U.card = k)
    (hmax : ∀ u : E, ‖u‖ = 1 → I ⊆ positiveSupport f u → positiveSupport f u = I)
    {w : E} (hw : ‖w‖ = 1) (hwi : ∀ i ∈ I, 0 < f w i) :
    ∃ u : E, ‖u‖ = 1 ∧ U ⊆ positiveSupport f u ∧ ¬ positiveSupport f u ⊆ I := by
  classical
  have hdiff : (I \ U).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_sdiff_of_subset hUI,hI,hU]
    omega
  obtain ⟨i,hi⟩ := hdiff
  have hiI := (Finset.mem_sdiff.mp hi).1
  have hiU := (Finset.mem_sdiff.mp hi).2
  let b : Fin (k+1) ≃ ↥I := (Fintype.equivFinOfCardEq (by simpa using hI)).symm
  let a : Fin (k+1) ≃ ↥I := (Equiv.swap 0 (b.symm ⟨i,hiI⟩)).trans b
  have ha : (a 0).val = i := by simp [a]
  obtain ⟨u,hu,hup,hnot⟩ := hf.no_free_indexed_facet hk hdim hn a hmax hw hwi
  refine ⟨u,hu,?_,hnot⟩
  intro j hj
  obtain ⟨l,hl⟩ := a.surjective ⟨j,hUI hj⟩
  have hlj : (a l).val = j := congrArg Subtype.val hl
  have hl0 : l ≠ 0 := by
    intro hl0
    rw [hl0,ha] at hlj
    exact hiU (hlj ▸ hj)
  obtain ⟨q,rfl⟩ := Fin.eq_succ_of_ne_zero hl0
  rw [← hlj]
  exact (mem_positiveSupport f u _).mpr (hup q)
end NoFreeRidge
end BorsukNine

end OAI
end

theorem solution.{u_1} : type_of% @OAI.BorsukNine.Admissible.no_free_ridge_oai.{u_1} := @OAI.BorsukNine.Admissible.no_free_ridge_oai.{u_1}
