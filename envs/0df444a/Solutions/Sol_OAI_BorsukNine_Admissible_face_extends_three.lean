-- Prove2me | solution 1 for OAI.BorsukNine.Admissible.face_extends_three
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T20:53:58.790057+00:00
-- url     : https://prove2.me/submissions/a14132b8-4ab5-4b24-8470-b1cf71c2c9d1

import Mathlib
import Definitions.Def_OAIQ058B000
import Theorems.Thm_OAI_BorsukNine_Admissible_chart_surgery_impossible

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
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h
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
-- module Solutions.OAIQ058_BK.Borsuk_Projectors_Basic
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine

open scoped RealInnerProductSpace ContDiff

open scoped Manifold

lemma Admissible.support_nonempty {ι : Type*} [Fintype ι]
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {f : V → ι → ℝ} (hf : Admissible f) {u : V} (hu : ‖u‖ = 1) :
    (positiveSupport f u).Nonempty := by
  classical
  have hs : 0 < ∑ i, f u i := by rw [hf.sum_one u hu]; norm_num
  obtain ⟨i, _, hi⟩ := (Finset.sum_pos_iff_of_nonneg (fun i _ => hf.nonneg u hu i)).mp hs
  exact ⟨i, (mem_positiveSupport f u i).mpr hi⟩

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

lemma Admissible.lift_orthogonal {f : V → ι → ℝ} (hf : Admissible f)
    {u v : V} (huv : ⟪u, v⟫ = 0) (i : ι) :
    homogeneousLift f u i * homogeneousLift f v i = 0 := by
  by_cases hu : u = 0
  · simp [hu]
  by_cases hv : v = 0
  · simp [hv]
  have hn : ⟪(‖u‖⁻¹ : ℝ) • u, (‖v‖⁻¹ : ℝ) • v⟫ = 0 := by
    simp [inner_smul_left, inner_smul_right, huv]
  have h := hf.orthogonal _ _ (norm_smul_inv_norm (𝕜 := ℝ) hu) (norm_smul_inv_norm (𝕜 := ℝ) hv) hn i
  have hnu := hf.nonneg _ (norm_smul_inv_norm (𝕜 := ℝ) hu) i
  have hnv := hf.nonneg _ (norm_smul_inv_norm (𝕜 := ℝ) hv) i
  have hz : f ((‖u‖⁻¹ : ℝ) • u) i = 0 ∨ f ((‖v‖⁻¹ : ℝ) • v) i = 0 := by
    by_contra hh
    push Not at hh
    exact h ⟨lt_of_le_of_ne hnu (Ne.symm hh.1), lt_of_le_of_ne hnv (Ne.symm hh.2)⟩
  rcases hz with hz | hz <;> simp [homogeneousLift, hz]
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
-- module Solutions.OAIQ058_BK.Borsuk_Support_Chambers
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace
section Chambers
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma mem_signChamber_self {Z : Set E} {c : E} (hc : c ∈ safeNormals Z) :
    c ∈ signChamber Z c := by
  intro z hz
  exact mul_self_pos.mpr (hc z hz)

lemma signChamber_eq_of_mem {Z : Set E} {c d x : E}
    (hc : x ∈ signChamber Z c) (hd : x ∈ signChamber Z d) :
    signChamber Z c = signChamber Z d := by
  ext y
  constructor <;> intro hy z hz
  · have h1 := hc z hz
    have h2 := hd z hz
    have h3 := hy z hz
    rcases mul_pos_iff.mp h1 with h1 | h1 <;>
      rcases mul_pos_iff.mp h2 with h2 | h2 <;>
      rcases mul_pos_iff.mp h3 with h3 | h3
    all_goals first | exact mul_pos h2.1 h3.2 | exact mul_pos_of_neg_of_neg h2.1 h3.2 | linarith [h1.1,h1.2,h2.1,h2.2,h3.1,h3.2]
  · have h1 := hc z hz
    have h2 := hd z hz
    have h3 := hy z hz
    rcases mul_pos_iff.mp h1 with h1 | h1 <;>
      rcases mul_pos_iff.mp h2 with h2 | h2 <;>
      rcases mul_pos_iff.mp h3 with h3 | h3
    all_goals first | exact mul_pos h1.1 h3.2 | exact mul_pos_of_neg_of_neg h1.1 h3.2 | linarith [h1.1,h1.2,h2.1,h2.2,h3.1,h3.2]

lemma signChamber_eq_or_disjoint (Z : Set E) (c d : E) :
    signChamber Z c = signChamber Z d ∨ Disjoint (signChamber Z c) (signChamber Z d) := by
  by_cases h : Disjoint (signChamber Z c) (signChamber Z d)
  · exact Or.inr h
  · rw [Set.disjoint_left] at h
    push Not at h
    obtain ⟨x,hc,hd⟩ := h
    exact Or.inl (signChamber_eq_of_mem hc hd)

lemma interior_safe_mem_chamber {Z : Set E} {c x : E}
    (hx : x ∈ interior (safeNormals Z)) (hxc : x ∈ signChamber Z c) :
    x ∈ interior (signChamber Z c) := by
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx)
  apply mem_interior_iff_mem_nhds.mpr
  apply Filter.mem_of_superset (Metric.ball_mem_nhds x hε)
  intro y hy z hz
  have hc := hxc z hz
  have hn : ∀ w ∈ Metric.ball x ε, ⟪w,z⟫ ≠ 0 := fun w hw => hball hw z hz
  have hf : ContinuousOn (fun w : E => ⟪w,z⟫) (Metric.ball x ε) :=
    (continuous_id.inner continuous_const).continuousOn
  have hxball : x ∈ Metric.ball x ε := Metric.mem_ball_self hε
  rcases mul_pos_iff.mp hc with hc | hc
  · exact mul_pos hc.1 ((convex_ball x ε).isPreconnected.lt_of_ne hf hn ⟨x,hxball,hc.2⟩ hy)
  · exact mul_pos_of_neg_of_neg hc.1 ((convex_ball x ε).isPreconnected.gt_of_ne hf hn ⟨x,hxball,hc.2⟩ hy)

lemma interior_safe_mem_own_chamber {Z : Set E} {c : E}
    (hc : c ∈ interior (safeNormals Z)) : c ∈ interior (signChamber Z c) :=
  interior_safe_mem_chamber hc (mem_signChamber_self (interior_subset hc))

lemma compact_finite_chambers {Z K : Set E} (hK : IsCompact K)
    (hsub : K ⊆ interior (safeNormals Z)) :
    ∃ C : Finset E, (↑C : Set E) ⊆ K ∧ K ⊆ ⋃ c ∈ (↑C : Set E), interior (signChamber Z c) := by
  classical
  obtain ⟨C,hCK,hCf,hcover⟩ := hK.elim_finite_subcover_image
    (b := K) (c := fun c : E => interior (signChamber Z c)) (fun _ _ => isOpen_interior)
    (fun c hc => Set.mem_iUnion₂.mpr ⟨c,hc,interior_safe_mem_own_chamber (hsub hc)⟩)
  exact ⟨hCf.toFinset,by simpa using hCK,by simpa using hcover⟩

end Chambers
end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Simplicial_Equivariance
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset
variable {V : Type*} [DecidableEq V]

section Cone

lemma cone_simplex (K : PreAbstractSimplicialComplex V) (a : V) {s : Finset V} (hs : s ∈ K) :
    cone K a (simplex K s) = if a ∈ s then 0 else simplex K (insert a s) := by
  simp [simplex_of_mem K hs, cone, Finsupp.linearCombination_single]

lemma cone_boundary_simplex (K : PreAbstractSimplicialComplex V) (a : V)
    {s : Finset V} (hs : s ∈ K) (hinsert : insert a s ∈ K) (ha : a ∉ s) :
    boundary K (cone K a (simplex K s)) = simplex K s + cone K a (boundary K (simplex K s)) +
      augmentation K (simplex K s) • simplex K {a} := by
  classical
  by_cases hc : s.card = 1
  · obtain ⟨b, rfl⟩ := Finset.card_eq_one.mp hc
    have hab : a ≠ b := by simpa using ha
    have hs' : ({a} : Finset V) ∈ K :=
      (K.isRelLowerSet_faces hinsert).2 (by simp) (Finset.singleton_nonempty a)
    rw [cone_simplex K a hs, ite_eq_right ha, boundary_simplex K hinsert,
      boundary_simplex K hs, augmentation_simplex K hs]
    simp [ha, Finset.erase_insert_of_ne hab]
  · have hn : s.Nonempty := (K.isRelLowerSet_faces hs).1
    have hc' : 2 ≤ s.card := by have := hn.card_pos; omega
    have he (b : V) (hb : b ∈ s) : (s.erase b).Nonempty := by
      rw [← Finset.card_pos, Finset.card_erase_of_mem hb]
      omega
    have heK (b : V) (hb : b ∈ s) : s.erase b ∈ K :=
      (K.isRelLowerSet_faces hs).2 (Finset.erase_subset b s) (he b hb)
    rw [cone_simplex K a hs, ite_eq_right ha, boundary_simplex K hinsert,
      augmentation_simplex K hs, ite_eq_right hc, zero_smul, add_zero,
      boundary_simplex K hs, map_sum, Finset.sum_insert ha, Finset.erase_insert ha]
    apply congrArg (fun z => simplex K s + z)
    apply Finset.sum_congr rfl
    intro b hb
    have hab : a ≠ b := by intro hh; subst b; exact ha hb
    have hn : a ∉ s.erase b := fun hh => ha (Finset.mem_of_mem_erase hh)
    rw [cone_simplex K a (heK b hb), ite_eq_right hn, Finset.erase_insert_of_ne hab]

lemma cone_boundary_simplex_all (K : PreAbstractSimplicialComplex V) (a : V)
    {s : Finset V} (hs : s ∈ K) (hinsert : insert a s ∈ K) :
    boundary K (cone K a (simplex K s)) = simplex K s + cone K a (boundary K (simplex K s)) +
      augmentation K (simplex K s) • simplex K {a} := by
  classical
  by_cases ha : a ∈ s
  · by_cases hc : s.card = 1
    · obtain ⟨b, rfl⟩ := Finset.card_eq_one.mp hc
      have hab : a = b := Finset.mem_singleton.mp ha
      subst b
      rw [cone_simplex K a hs, ite_eq_left ha, map_zero, boundary_simplex K hs,
        augmentation_simplex K hs]
      simp [chain_add_self]
    · have hcn (b : V) (hb : b ∈ s) : (s.erase b).Nonempty := by
        have hn := (K.isRelLowerSet_faces hs).1.card_pos
        rw [← Finset.card_pos, Finset.card_erase_of_mem hb]
        omega
      have hcon : cone K a (boundary K (simplex K s)) = simplex K s := by
        rw [boundary_simplex K hs, map_sum]
        rw [Finset.sum_eq_single a]
        · rw [cone_simplex K a ((K.isRelLowerSet_faces hs).2 (Finset.erase_subset a s) (hcn a ha))]
          simp [Finset.insert_erase ha]
        · intro b hb hba
          rw [cone_simplex K a ((K.isRelLowerSet_faces hs).2 (Finset.erase_subset b s) (hcn b hb))]
          simp [Finset.mem_erase.mpr ⟨Ne.symm hba, ha⟩]
        · exact fun hn => False.elim (hn ha)
      rw [cone_simplex K a hs, ite_eq_left ha, map_zero, hcon,
        augmentation_simplex K hs, ite_eq_right hc, zero_smul, add_zero, chain_add_self]
  · exact cone_boundary_simplex K a hs hinsert ha

omit [DecidableEq V] in
lemma chain_eq_sum (K : PreAbstractSimplicialComplex V) (c : Chain K) :
    c = ∑ s ∈ c.support, c s • simplex K s.val := by
  conv_lhs => rw [← c.sum_single]
  simp [Finsupp.sum, simplex_of_mem K, Finsupp.smul_single]

lemma cone_boundary (K : PreAbstractSimplicialComplex V) (a : V) (c : Chain K)
    (hc : ∀ s ∈ c.support, insert a s.val ∈ K) :
    boundary K (cone K a c) = c + cone K a (boundary K c) +
      augmentation K c • simplex K {a} := by
  classical
  conv_lhs => rw [chain_eq_sum K c]
  rw [map_sum, map_sum]
  have he (s : { s : Finset V // s ∈ K }) (hs : s ∈ c.support) :
      boundary K (cone K a (c s • simplex K s.val)) =
        c s • simplex K s.val + cone K a (boundary K (c s • simplex K s.val)) +
        augmentation K (c s • simplex K s.val) • simplex K {a} := by
    rw [map_smul, map_smul, cone_boundary_simplex_all K a s.property (hc s hs)]
    simp only [smul_add, map_smul, smul_smul, smul_eq_mul]
  rw [Finset.sum_congr rfl he, Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [← map_sum, ← map_sum, ← Finset.sum_smul, ← map_sum, ← chain_eq_sum K c]

end Cone

end BorsukNine.SimplicialChains

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_SmithTheory_Involution
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine.SmithTheory
variable {K P Q : Type*} [Field K] [AddCommGroup P] [Module K P]
  [AddCommGroup Q] [Module K Q]
section Involution
variable {ι : Type*}

lemma involutionNorm_sq (τ : ι ≃ ι) (hτ : Function.Involutive τ) :
    (involutionNorm τ).comp (involutionNorm τ) = 0 := by
  apply LinearMap.ext
  intro c
  apply Finsupp.ext
  intro a
  have ht (a : ι) : τ (τ a) = a := hτ a
  have hsymm (a : ι) : τ.symm a = τ a := by
    apply τ.injective
    rw [τ.apply_symm_apply, ht]
  simp only [LinearMap.comp_apply, involutionNorm_apply, hsymm, ht,
    LinearMap.zero_apply, Finsupp.zero_apply]
  simp [add_comm, CharTwo.add_self_eq_zero]

end Involution

end BorsukNine.SmithTheory

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_MatrixGeometry_SymmetricCoordinates
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
section SymmetricCoordinates
variable {ν : Type*} [Fintype ν] [LinearOrder ν]

omit [Fintype ν] in
lemma symmetricCoordinates_upper (x : EuclideanSpace ℝ (UpperTriangle ν))
    (i j : ν) (hij : i ≤ j) : symmetricCoordinates x i j = x ⟨(i,j), hij⟩ := by
  change (if h : i ≤ j then x ⟨(i,j),h⟩ else x ⟨(j,i),le_of_not_ge h⟩) = _
  exact dite_eq_left hij

omit [Fintype ν] in
lemma symmetricCoordinates_selfAdjoint (x : EuclideanSpace ℝ (UpperTriangle ν)) :
    IsSelfAdjoint (symmetricCoordinates x) := by
  change (symmetricCoordinates x)ᴴ = symmetricCoordinates x
  ext i j
  simp only [Matrix.conjTranspose_apply, star_trivial]
  change (if h : j ≤ i then x ⟨(j,i),h⟩ else x ⟨(i,j),le_of_not_ge h⟩) =
    (if h : i ≤ j then x ⟨(i,j),h⟩ else x ⟨(j,i),le_of_not_ge h⟩)
  by_cases hij : i ≤ j
  · by_cases hji : j ≤ i
    · have he := le_antisymm hij hji
      subst j
      rfl
    · simp [hij, hji]
  · have hji : j ≤ i := le_of_not_ge hij
    simp [hij, hji]

omit [Fintype ν] in
lemma symmetricCoordinates_injective : Function.Injective (symmetricCoordinates (ν := ν)) := by
  intro x y hxy
  apply PiLp.ext
  intro p
  have h := congrArg (fun A : Matrix ν ν ℝ => A p.val.1 p.val.2) hxy
  simpa only [symmetricCoordinates_upper _ _ _ p.property] using h

end SymmetricCoordinates

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

lemma Admissible.normalizedSignedExtension_norm {f : E → ι → ℝ} (hf : Admissible f)
    {A : Matrix ν ν ℝ} (hA : IsSelfAdjoint A) (hneq : A ≠ 0) :
    ‖normalizedSignedExtension f A‖ = 1 := by
  have hn : WithLp.toLp 2 (signedExtension f A) ≠ 0 := by
    intro hz
    have hs : signedExtension f A = 0 := WithLp.toLp_injective 2 hz
    exact hneq ((hf.signedExtension_eq_zero_iff hA).mp hs)
  simp [normalizedSignedExtension, norm_smul, norm_inv, hn]

omit [Nonempty ν] in
lemma normalizedSignedExtension_odd (f : E → ι → ℝ) (A : Matrix ν ν ℝ) :
    normalizedSignedExtension f (-A) = -normalizedSignedExtension f A := by
  simp [normalizedSignedExtension, signedExtension_odd, WithLp.toLp_neg]

lemma Admissible.normalizedSignedExtension_continuousOn {f : E → ι → ℝ} (hf : Admissible f) :
    ContinuousOn (normalizedSignedExtension f) {A : Matrix ν ν ℝ | IsSelfAdjoint A ∧ A ≠ 0} := by
  have hc : ContinuousOn (fun A : Matrix ν ν ℝ => WithLp.toLp 2 (signedExtension f A))
      {A | IsSelfAdjoint A ∧ A ≠ 0} :=
    (PiLp.continuous_toLp 2 _).comp_continuousOn
      (hf.signedExtension_continuousOn.mono (fun _ h => h.1))
  apply ContinuousOn.smul (ContinuousOn.inv₀ hc.norm _) hc
  intro A hA
  rw [norm_ne_zero_iff]
  intro hh
  have hs : signedExtension f A = 0 := WithLp.toLp_injective 2 hh
  exact hA.2 ((hf.signedExtension_eq_zero_iff hA.1).mp hs)

end SphereExtension

end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_SphereGeometry_OddSphereMap
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
section OddSphereMap
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {ν ι : Type*} [Fintype ν] [LinearOrder ν] [Nonempty ν] [Fintype ι]
local notation "E" => EuclideanSpace ℝ ν

lemma Admissible.sphereExtension_norm {f : E → ι → ℝ} (hf : Admissible f)
    {x : EuclideanSpace ℝ (UpperTriangle ν)} (hx : ‖x‖ = 1) : ‖sphereExtension f x‖ = 1 := by
  apply hf.normalizedSignedExtension_norm (symmetricCoordinates_selfAdjoint x)
  intro hh
  have hn : x = 0 := symmetricCoordinates_injective (hh.trans (map_zero _).symm)
  simp [hn] at hx

omit [Nonempty ν] in
lemma sphereExtension_odd (f : E → ι → ℝ) (x : EuclideanSpace ℝ (UpperTriangle ν)) :
    sphereExtension f (-x) = -sphereExtension f x := by
  simp only [sphereExtension, map_neg, normalizedSignedExtension_odd]

lemma Admissible.sphereExtension_continuousOn {f : E → ι → ℝ} (hf : Admissible f) :
    ContinuousOn (sphereExtension f) {x : EuclideanSpace ℝ (UpperTriangle ν) | ‖x‖ = 1} := by
  apply hf.normalizedSignedExtension_continuousOn.comp
    (symmetricCoordinates.continuous_of_finiteDimensional.continuousOn) (fun x hx => ?_)
  refine ⟨symmetricCoordinates_selfAdjoint x, ?_⟩
  intro hh
  have hn : x = 0 := symmetricCoordinates_injective (hh.trans (map_zero _).symm)
  simp [hn] at hx

end OddSphereMap

end BorsukNine

namespace BorsukNine.SmithTheory

variable {K P Q : Type*} [Field K] [AddCommGroup P] [Module K P]
  [AddCommGroup Q] [Module K Q]

lemma tower_augmentation_zero (d N : P →ₗ[K] P)
    (hd : d.comp d = 0) (hcomm : d.comp N = N.comp d)
    (hexact : LinearMap.ker N ≤ LinearMap.range N)
    (n : ℕ) (φ : P →ₗ[K] Q) (hφN : φ.comp N = 0) (hφd : φ.comp d = 0)
    (c : ℕ → P) (htower : ∀ i < n, d (c (i + 1)) = N (c i))
    (htop : N (c n) = 0) : φ (c 0) = 0 := by
  induction n generalizing φ c with
  | zero =>
    obtain ⟨ψ, hψ⟩ := exists_factor_of_vanish_norm N hexact φ hφN
    rw [← hψ, LinearMap.comp_apply, htop, map_zero]
  | succ n ih =>
    obtain ⟨ψ, hψ⟩ := exists_factor_of_vanish_norm N hexact φ hφN
    have hN : (ψ.comp d).comp N = 0 := by
      rw [LinearMap.comp_assoc, hcomm, ← LinearMap.comp_assoc, hψ, hφd]
    have hd' : (ψ.comp d).comp d = 0 := by
      rw [LinearMap.comp_assoc, hd, LinearMap.comp_zero]
    have hh := ih (ψ.comp d) hN hd' (fun i => c (i + 1))
      (fun i hi => htower (i + 1) (Nat.add_lt_add_right hi 1)) htop
    rw [← hψ, LinearMap.comp_apply, ← htower 0 (Nat.zero_lt_succ n)]
    exact hh

end BorsukNine.SmithTheory

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Simplicial_NormMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset
variable {V W : Type*} [DecidableEq V] [DecidableEq W]

lemma antipodal_tower_augmentation_zero (K : PreAbstractSimplicialComplex V)
    (e : V ≃ V) (he : ∀ s, s ∈ K ↔ s.image e ∈ K) (hi : Function.Involutive e)
    (hfree : ∀ s ∈ K, s.image e ≠ s)
    (n : ℕ) (c : ℕ → Chain K)
    (htower : ∀ i < n, boundary K (c (i+1)) = normMap K e (c i))
    (htop : normMap K e (c n) = 0) : augmentation K (c 0) = 0 := by
  apply SmithTheory.tower_augmentation_zero (boundary K) (normMap K e)
    (boundary_sq K) (boundary_normMap K e (fun s hs => (he s).mp hs))
    _ n (augmentation K) (augmentation_normMap K e (fun s hs => (he s).mp hs))
    (augmentation_boundary K) c htower htop
  rw [normMap_eq K e he]
  exact SmithTheory.involutionNorm_exact _ (faceEquiv_involutive K e he hi)
    (faceEquiv_free K e he hfree)

omit [DecidableEq V] in
lemma simplex_mem_degree (K : PreAbstractSimplicialComplex V) {s : Finset V}
    (hs : s ∈ K) : simplex K s ∈ degreeChains K s.card := by
  rw [simplex_of_mem K hs]
  exact Finsupp.single_mem_supported _ _ rfl

omit [DecidableEq V] [DecidableEq W] in
lemma grade_map (K : PreAbstractSimplicialComplex V) (L : PreAbstractSimplicialComplex W)
    (T : Chain K →ₗ[F₂] Chain L) (d e : ℕ)
    (hT : ∀ s ∈ K, s.card = d → T (simplex K s) ∈ degreeChains L e) :
    degreeChains K d ≤ (degreeChains L e).comap T := by
  rw [degreeChains, Finsupp.supported_eq_span_single]
  apply Submodule.span_le.mpr
  rintro _ ⟨s, hs, rfl⟩
  change T (Finsupp.single s 1) ∈ degreeChains L e
  rw [← simplex_of_mem K s.property]
  exact hT s.val s.property hs

omit [DecidableEq V] in
lemma mapChains_degree (K : PreAbstractSimplicialComplex V) (L : PreAbstractSimplicialComplex W)
    (f : V → W) (hf : ∀ s ∈ K, s.image f ∈ L) (d : ℕ) :
    degreeChains K d ≤ (degreeChains L d).comap (mapChains K L f) := by
  apply grade_map K L _ d d
  intro s hs hd
  rw [mapChains_simplex K L f hs, mapSimplex]
  split_ifs with hh
  · rw [← hd, ← hh]
    exact simplex_mem_degree L (hf s hs)
  · exact Submodule.zero_mem _

omit [DecidableEq V] in
lemma degreeChains_eq_bot_of_card_bound (K : PreAbstractSimplicialComplex V) (d : ℕ)
    (hK : ∀ s ∈ K, s.card < d) : degreeChains K d = ⊥ := by
  apply eq_bot_iff.mpr
  intro c hc
  apply Finsupp.ext
  intro s
  have hne : s.val.card ≠ d := ne_of_lt (hK s.val s.property)
  exact (Finsupp.mem_supported' F₂ c).mp hc s hne

omit [DecidableEq V] in
lemma augmentation_eq_zero_of_degree (K : PreAbstractSimplicialComplex V) (d : ℕ)
    (hd : d ≠ 1) {c : Chain K} (hc : c ∈ degreeChains K d) : augmentation K c = 0 := by
  have hle : degreeChains K d ≤ LinearMap.ker (augmentation K) := by
    rw [degreeChains, Finsupp.supported_eq_span_single]
    apply Submodule.span_le.mpr
    rintro _ ⟨s, hs, rfl⟩
    change augmentation K (Finsupp.single s 1) = 0
    rw [← simplex_of_mem K s.property, augmentation_simplex K s.property]
    simp [show s.val.card ≠ 1 by simpa only [Set.mem_ofPred_eq] using hs ▸ hd]
  exact hle hc

end BorsukNine.SimplicialChains

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Simplicial_MemSupportSimplex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset
variable {V W : Type*} [DecidableEq V] [DecidableEq W]

omit [DecidableEq V] in
lemma mem_support_simplex (K : PreAbstractSimplicialComplex V) (s : Finset V)
    (t : {s : Finset V // s ∈ K}) :
    t ∈ (simplex K s).support ↔ t.val = s := by
  classical
  by_cases hs : s ∈ K
  · rw [simplex_of_mem K hs, Finsupp.support_single _ one_ne_zero]
    simp only [Finset.mem_singleton, Subtype.ext_iff]
  · simp only [simplex, dite_eq_right hs, Finsupp.support_zero, Finset.notMem_empty, false_iff]
    intro he
    exact hs (he ▸ t.property)

omit [DecidableEq V] [DecidableEq W] in
lemma support_linearMap (K : PreAbstractSimplicialComplex V) (L : PreAbstractSimplicialComplex W)
    (T : Chain K →ₗ[F₂] Chain L) (c : Chain K)
    {t : {s : Finset W // s ∈ L}} (ht : t ∈ (T c).support) :
    ∃ s ∈ c.support, t ∈ (T (simplex K s.val)).support := by
  classical
  by_contra hn
  push Not at hn
  have hh : (T c) t = 0 := by
    conv_lhs => rw [chain_eq_sum K c]
    rw [map_sum, Finsupp.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro s hs
    rw [map_smul, Finsupp.smul_apply, Finsupp.notMem_support_iff.mp (hn s hs), smul_zero]
  exact (Finsupp.mem_support_iff.mp ht) hh

lemma support_cone (K : PreAbstractSimplicialComplex V) (a : V) (c : Chain K)
    {t : {s : Finset V // s ∈ K}} (ht : t ∈ (cone K a c).support) :
    ∃ s ∈ c.support, a ∉ s.val ∧ t.val = insert a s.val := by
  obtain ⟨s, hs, ht⟩ := support_linearMap K K (cone K a) c ht
  rw [cone_simplex K a s.property] at ht
  split_ifs at ht with ha
  · simp at ht
  · exact ⟨s, hs, ha, (mem_support_simplex K _ t).mp ht⟩

lemma cone_degree (K : PreAbstractSimplicialComplex V) (a : V) (d : ℕ) :
    degreeChains K d ≤ (degreeChains K (d+1)).comap (cone K a) := by
  intro c hc t ht
  obtain ⟨s, hs, ha, he⟩ := support_cone K a c ht
  change t.val.card = d+1
  rw [he, Finset.card_insert_of_notMem ha, hc hs]

end BorsukNine.SimplicialChains

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Simplicial_SubdivSimplex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset
variable {V W : Type*} [DecidableEq V] [DecidableEq W]

lemma subdivSimplex_one (L : PreAbstractSimplicialComplex W) (b : Finset V → W)
    {s : Finset V} (hc : s.card = 1) : subdivSimplex L b s = simplex L {b s} := by
  have hn : s.Nonempty := Finset.card_pos.mp (by omega)
  rw [subdivSimplex, dite_eq_left hn, ite_eq_left hc]

lemma subdivSimplex_many (L : PreAbstractSimplicialComplex W) (b : Finset V → W)
    {s : Finset V} (hn : s.Nonempty) (hc : s.card ≠ 1) :
    subdivSimplex L b s = cone L (b s) (∑ a ∈ s, subdivSimplex L b (s.erase a)) := by
  rw [subdivSimplex, dite_eq_left hn, ite_eq_right hc]
  exact congrArg (cone L (b s)) (Finset.sum_attach s (fun a : V => subdivSimplex L b (s.erase a)))

omit [DecidableEq V] [DecidableEq W] in
lemma vertexCarrier_mono (b : Finset V → W) {s t : Finset V} (hst : s ⊆ t) :
    vertexCarrier b s ⊆ vertexCarrier b t := by
  rintro w ⟨u, hu, hus, hb⟩
  exact ⟨u, hu, hus.trans hst, hb⟩

omit [DecidableEq V] [DecidableEq W] in
lemma center_mem_carrier (b : Finset V → W) {s : Finset V} (hs : s.Nonempty) :
    b s ∈ vertexCarrier b s := ⟨s, hs, Finset.Subset.refl _, rfl⟩

lemma support_sum_chains (L : PreAbstractSimplicialComplex W) {α : Type*}
    (s : Finset α) (c : α → Chain L) {t : {s : Finset W // s ∈ L}}
    (ht : t ∈ (∑ a ∈ s, c a).support) : ∃ a ∈ s, t ∈ (c a).support := by
  classical
  by_contra hn
  push Not at hn
  have hh : (∑ a ∈ s, c a) t = 0 := by
    rw [Finsupp.finsetSum_apply]
    exact Finset.sum_eq_zero (fun a ha => Finsupp.notMem_support_iff.mp (hn a ha))
  exact Finsupp.mem_support_iff.mp ht hh

lemma subdivSimplex_carrier (L : PreAbstractSimplicialComplex W) (b : Finset V → W)
    (s : Finset V) {t : {s : Finset W // s ∈ L}}
    (ht : t ∈ (subdivSimplex L b s).support) : ↑t.val ⊆ vertexCarrier b s := by
  induction s using Finset.strongInductionOn generalizing t with
  | _ s ih =>
    rcases s.eq_empty_or_nonempty with rfl | hn
    · simp at ht
    by_cases hc : s.card = 1
    · rw [subdivSimplex_one L b hc, mem_support_simplex] at ht
      rw [ht]
      exact Finset.singleton_subset_set_iff.mpr (center_mem_carrier b hn)
    · rw [subdivSimplex_many L b hn hc] at ht
      obtain ⟨u, hu, _, htu⟩ := support_cone L (b s) _ ht
      obtain ⟨a, ha, hua⟩ := support_sum_chains L s _ hu
      have hu' := ih (s.erase a) (Finset.erase_ssubset ha) hua
      rw [htu, Finset.coe_insert]
      exact Set.insert_subset (center_mem_carrier b hn)
        (hu'.trans (vertexCarrier_mono b (Finset.erase_subset a s)))

end BorsukNine.SimplicialChains

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Simplicial_SimplexMemDegreeAll
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset
variable {V W : Type*} [DecidableEq V] [DecidableEq W]

omit [DecidableEq V] in
lemma simplex_mem_degree_all (K : PreAbstractSimplicialComplex V) (s : Finset V) :
    simplex K s ∈ degreeChains K s.card := by
  classical
  by_cases hs : s ∈ K
  · exact simplex_mem_degree K hs
  · simp only [simplex, dite_eq_right hs]
    exact Submodule.zero_mem _

lemma subdivSimplex_degree (L : PreAbstractSimplicialComplex W) (b : Finset V → W)
    (s : Finset V) : subdivSimplex L b s ∈ degreeChains L s.card := by
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    rcases s.eq_empty_or_nonempty with rfl | hn
    · rw [subdivSimplex_empty]
      exact Submodule.zero_mem _
    by_cases hc : s.card = 1
    · rw [subdivSimplex_one L b hc, hc]
      exact simplex_mem_degree_all L {b s}
    · rw [subdivSimplex_many L b hn hc]
      have hsum : (∑ a ∈ s, subdivSimplex L b (s.erase a)) ∈ degreeChains L (s.card-1) := by
        apply Submodule.sum_mem
        intro a ha
        have hh := ih (s.erase a) (Finset.erase_ssubset ha)
        simpa only [Finset.card_erase_of_mem ha] using hh
      have hpos := hn.card_pos
      simpa only [Submodule.mem_comap, Nat.sub_add_cancel hpos] using
        cone_degree L (b s) (s.card-1) hsum

omit [DecidableEq V] [DecidableEq W] in
lemma SubdivisionCarrier.center (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (b : Finset V → W) (hb : SubdivisionCarrier K L b)
    {s : Finset V} (hs : s ∈ K) : {b s} ∈ L :=
  hb s hs {b s} (Finset.singleton_nonempty _) (Finset.singleton_subset_set_iff.mpr
    (center_mem_carrier b (K.isRelLowerSet_faces hs).1))

lemma subdivSimplex_augmentation (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (b : Finset V → W) (hb : SubdivisionCarrier K L b)
    {s : Finset V} (hs : s ∈ K) :
    augmentation L (subdivSimplex L b s) = augmentation K (simplex K s) := by
  rw [augmentation_simplex K hs]
  by_cases hc : s.card = 1
  · rw [subdivSimplex_one L b hc, augmentation_simplex L (hb.center K L b hs)]
    simp [hc]
  · rw [ite_eq_right hc]
    exact augmentation_eq_zero_of_degree L _ hc (subdivSimplex_degree L b s)

lemma subdivMap_simplex (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (b : Finset V → W) {s : Finset V} (hs : s ∈ K) :
    subdivMap K L b (simplex K s) = subdivSimplex L b s := by
  simp [simplex_of_mem K hs, subdivMap, Finsupp.linearCombination_single]

lemma subdivMap_simplex_subset (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (b : Finset V → W) {s t : Finset V}
    (ht : t ∈ K) (hs : s ⊆ t) : subdivMap K L b (simplex K s) = subdivSimplex L b s := by
  rcases s.eq_empty_or_nonempty with rfl | hn
  · simp
  · exact subdivMap_simplex K L b ((K.isRelLowerSet_faces ht).2 hs hn)

lemma subdivMap_augmentation (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (b : Finset V → W) (hb : SubdivisionCarrier K L b) :
    (augmentation L).comp (subdivMap K L b) = augmentation K := by
  apply Finsupp.lhom_ext
  intro s r
  have hs := subdivSimplex_augmentation K L b hb s.property
  have hm := subdivMap_simplex K L b s.property
  rw [simplex_of_mem K s.property] at hs hm
  have he : Finsupp.single s r = r • Finsupp.single s (1 : F₂) := by simp
  simp only [LinearMap.comp_apply, he, map_smul, hm, hs]

lemma subdivMap_boundary_simplex (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (b : Finset V → W) {s : Finset V} (hs : s ∈ K) :
    subdivMap K L b (boundary K (simplex K s)) =
      ∑ a ∈ s, subdivSimplex L b (s.erase a) := by
  rw [boundary_simplex K hs, map_sum]
  apply Finset.sum_congr rfl
  intro a _
  exact subdivMap_simplex_subset K L b hs (Finset.erase_subset a s)

lemma subdivSimplex_boundary (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (b : Finset V → W) (hb : SubdivisionCarrier K L b)
    {s : Finset V} (hs : s ∈ K) :
    boundary L (subdivSimplex L b s) = subdivMap K L b (boundary K (simplex K s)) := by
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    have hn := (K.isRelLowerSet_faces hs).1
    by_cases hc : s.card = 1
    · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hc
      rw [subdivSimplex_one L b hc, boundary_simplex L (hb.center K L b hs),
        boundary_simplex K hs]
      simp
    · have hd : boundary L (subdivMap K L b (boundary K (simplex K s))) = 0 := by
        have he : boundary L (subdivMap K L b (boundary K (simplex K s))) =
            subdivMap K L b (boundary K (boundary K (simplex K s))) := by
          rw [boundary_simplex K hs]
          simp only [map_sum]
          apply Finset.sum_congr rfl
          intro a ha
          rcases (s.erase a).eq_empty_or_nonempty with heq | hne
          · simp [heq]
          · have hK : s.erase a ∈ K := (K.isRelLowerSet_faces hs).2 (Finset.erase_subset a s) hne
            rw [subdivMap_simplex K L b hK]
            exact ih (s.erase a) (Finset.erase_ssubset ha) hK
        rw [he, boundary_twice_simplex K hs, map_zero]
      have hε : augmentation L (subdivMap K L b (boundary K (simplex K s))) = 0 := by
        have hh := LinearMap.congr_fun (subdivMap_augmentation K L b hb)
          (boundary K (simplex K s))
        rw [LinearMap.comp_apply, augmentation_boundary_simplex K hs] at hh
        exact hh
      have hcone : ∀ t ∈ (subdivMap K L b (boundary K (simplex K s))).support,
          insert (b s) t.val ∈ L := by
        rw [subdivMap_boundary_simplex K L b hs]
        intro t ht
        obtain ⟨a, ha, hta⟩ := support_sum_chains L s _ ht
        have ht' := (subdivSimplex_carrier L b _ hta).trans
          (vertexCarrier_mono b (Finset.erase_subset a s))
        apply hb s hs _ (Finset.insert_nonempty _ _)
        rw [Finset.coe_insert]
        exact Set.insert_subset (center_mem_carrier b hn) ht'
      rw [subdivSimplex_many L b hn hc, ← subdivMap_boundary_simplex K L b hs,
        cone_boundary L (b s) _ hcone, hd, hε, map_zero, zero_smul, add_zero, add_zero]

lemma subdivMap_boundary (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (b : Finset V → W) (hb : SubdivisionCarrier K L b) :
    (boundary L).comp (subdivMap K L b) = (subdivMap K L b).comp (boundary K) := by
  apply Finsupp.lhom_ext
  intro s r
  have hs := subdivSimplex_boundary K L b hb s.property
  have hm := subdivMap_simplex K L b s.property
  rw [simplex_of_mem K s.property] at hs hm
  have he : Finsupp.single s r = r • Finsupp.single s (1 : F₂) := by simp
  simp only [LinearMap.comp_apply, he, map_smul, hm, hs]

end BorsukNine.SimplicialChains

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Simplicial_SignedVertex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset

lemma cross_card (n : ℕ) (s : Finset SignedVertex) (hs : s ∈ cross n) : s.card ≤ n := by
  calc
    s.card = (s.image Prod.fst).card := (Finset.card_image_iff.mpr hs.2.2).symm
    _ ≤ (Finset.range n).card := Finset.card_le_card (by
      intro i hi
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hi
      exact Finset.mem_range.mpr (hs.2.1 v hv))
    _ = n := Finset.card_range n

lemma cross_singleton (n i : ℕ) (hi : i < n) (b : Bool) :
    ({(i,b)} : Finset SignedVertex) ∈ cross n := by
  refine ⟨Finset.singleton_nonempty _, ?_, ?_⟩
  · simpa using hi
  · simpa only [Finset.coe_singleton] using Set.injOn_singleton Prod.fst (i,b)

lemma cross_insert (n i : ℕ) (hi : i < n) (s : Finset SignedVertex)
    (hs : s ∈ cross n) (hsi : ∀ v ∈ s, v.1 < i) (b : Bool) :
    insert (i,b) s ∈ cross n := by
  refine ⟨Finset.insert_nonempty _ _, ?_, ?_⟩
  · intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact hi
    · exact hs.2.1 v hv
  · intro v hv w hw he
    rcases Finset.mem_insert.mp hv with rfl | hv <;>
      rcases Finset.mem_insert.mp hw with rfl | hw
    · rfl
    · exact False.elim ((ne_of_lt (hsi w hw)) he.symm)
    · exact False.elim ((ne_of_lt (hsi v hv)) he)
    · exact hs.2.2 hv hw he

variable {V W : Type*} [DecidableEq V] [DecidableEq W]

omit [DecidableEq V] in
lemma support_mapChains_injective (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (f : V → W) (hf : Function.Injective f)
    (c : Chain K) {t : {s : Finset W // s ∈ L}}
    (ht : t ∈ (mapChains K L f c).support) :
    ∃ s ∈ c.support, t.val = s.val.image f := by
  obtain ⟨s, hs, hst⟩ := support_linearMap K L (mapChains K L f) c ht
  rw [mapChains_simplex K L f s.property, mapSimplex,
    ite_eq_left (Finset.card_image_iff.mpr hf.injOn), mem_support_simplex] at hst
  exact ⟨s, hs, hst⟩

lemma normMap_sq (K : PreAbstractSimplicialComplex V) (e : V ≃ V)
    (he : ∀ s, s ∈ K ↔ s.image e ∈ K) (hi : Function.Involutive e) :
    (normMap K e).comp (normMap K e) = 0 := by
  rw [normMap_eq K e he]
  exact SmithTheory.involutionNorm_sq _ (faceEquiv_involutive K e he hi)

lemma normMap_degree (K : PreAbstractSimplicialComplex V) (e : V ≃ V)
    (he : ∀ s ∈ K, s.image e ∈ K) (d : ℕ) :
    degreeChains K d ≤ (degreeChains K d).comap (normMap K e) := by
  intro c hc
  exact (degreeChains K d).add_mem hc (mapChains_degree K K e he d hc)

lemma crossTower_support (n i : ℕ) {s : {s : Finset SignedVertex // s ∈ cross n}}
    (hs : s ∈ (crossTower n i).support) : ∀ v ∈ s.val, v.1 ≤ i := by
  induction i generalizing s with
  | zero =>
    have he := (mem_support_simplex (cross n) {(0,false)} s).mp hs
    rw [he]
    intro v hv
    have he' := Finset.mem_singleton.mp hv
    exact he' ▸ Nat.le_refl 0
  | succ i ih =>
    obtain ⟨t, ht, _, he⟩ := support_cone (cross n) (i+1,false) _ hs
    rw [he]
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact le_rfl
    · have hu : t ∈ (crossTower n i).support ∪
          (mapChains (cross n) (cross n) flip (crossTower n i)).support :=
        Finsupp.support_add ht
      rcases Finset.mem_union.mp hu with ht | ht
      · exact (ih ht v hv).trans (Nat.le_succ i)
      · obtain ⟨u, hu, he⟩ := support_mapChains_injective (cross n) (cross n) flip
          flip.injective _ ht
        rw [he] at hv
        obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
        exact (ih hu w hw).trans (Nat.le_succ i)

lemma crossTower_degree (n i : ℕ) : crossTower n i ∈ degreeChains (cross n) (i+1) := by
  induction i with
  | zero => exact simplex_mem_degree_all (cross n) {(0,false)}
  | succ i ih =>
    exact cone_degree (cross n) (i+1,false) (i+1)
      (normMap_degree (cross n) flip (cross_flip_forward n) (i+1) ih)

lemma crossTower_cone_faces (n i : ℕ) (hi : i+1 < n)
    {s : {s : Finset SignedVertex // s ∈ cross n}}
    (hs : s ∈ (normMap (cross n) flip (crossTower n i)).support) :
    insert (i+1,false) s.val ∈ cross n := by
  apply cross_insert n (i+1) hi s.val s.property
  intro v hv
  have hu : s ∈ (crossTower n i).support ∪
      (mapChains (cross n) (cross n) flip (crossTower n i)).support :=
    Finsupp.support_add hs
  rcases Finset.mem_union.mp hu with hs | hs
  · exact Nat.lt_succ_of_le (crossTower_support n i hs v hv)
  · obtain ⟨t, ht, he⟩ := support_mapChains_injective (cross n) (cross n) flip
      flip.injective _ hs
    rw [he] at hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    exact Nat.lt_succ_of_le (crossTower_support n i ht w hw)

lemma crossTower_norm_boundary (n i : ℕ) (hi : i < n) :
    boundary (cross n) (normMap (cross n) flip (crossTower n i)) = 0 := by
  induction i with
  | zero =>
    have hc := LinearMap.congr_fun (boundary_normMap (cross n) flip (cross_flip_forward n))
      (crossTower n 0)
    rw [LinearMap.comp_apply, LinearMap.comp_apply] at hc
    rw [hc]
    change normMap (cross n) flip (boundary (cross n) (simplex (cross n) {(0,false)})) = 0
    rw [boundary_simplex (cross n) (cross_singleton n 0 hi false)]
    simp
  | succ i ih =>
    have hc := LinearMap.congr_fun (boundary_normMap (cross n) flip (cross_flip_forward n))
      (crossTower n (i+1))
    rw [LinearMap.comp_apply, LinearMap.comp_apply] at hc
    rw [hc]
    change normMap (cross n) flip (boundary (cross n)
      (cone (cross n) (i+1,false) (normMap (cross n) flip (crossTower n i)))) = 0
    rw [cone_boundary (cross n) _ _ (fun s hs => crossTower_cone_faces n i hi hs),
      ih (by omega)]
    have ha := LinearMap.congr_fun (augmentation_normMap (cross n) flip (cross_flip_forward n))
      (crossTower n i)
    rw [LinearMap.comp_apply, LinearMap.zero_apply] at ha
    rw [ha, map_zero, zero_smul, add_zero, add_zero]
    exact LinearMap.congr_fun (normMap_sq (cross n) flip (cross_flip n) flip_involutive) _

lemma crossTower_boundary (n i : ℕ) (hi : i+1 < n) :
    boundary (cross n) (crossTower n (i+1)) = normMap (cross n) flip (crossTower n i) := by
  change boundary (cross n) (cone (cross n) (i+1,false)
    (normMap (cross n) flip (crossTower n i))) = _
  rw [cone_boundary (cross n) _ _ (fun s hs => crossTower_cone_faces n i hi hs),
    crossTower_norm_boundary n i (by omega)]
  have ha := LinearMap.congr_fun (augmentation_normMap (cross n) flip (cross_flip_forward n))
    (crossTower n i)
  rw [LinearMap.comp_apply, LinearMap.zero_apply] at ha
  rw [ha, map_zero, zero_smul, add_zero, add_zero]

lemma crossTower_augmentation (n : ℕ) (hn : 0 < n) :
    augmentation (cross n) (crossTower n 0) = 1 := by
  rw [crossTower, augmentation_simplex (cross n) (cross_singleton n 0 hn false)]
  simp

end BorsukNine.SimplicialChains

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Simplicial_CrossChainDimensionBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine.SimplicialChains

lemma cross_chain_dimension_bound (n m : ℕ)
    (T : Chain (cross n) →ₗ[F₂] Chain (cross m))
    (hd : (boundary (cross m)).comp T = T.comp (boundary (cross n)))
    (hN : (normMap (cross m) flip).comp T = T.comp (normMap (cross n) flip))
    (ha : (augmentation (cross m)).comp T = augmentation (cross n))
    (hgrade : ∀ d, degreeChains (cross n) d ≤ (degreeChains (cross m) d).comap T) :
    n ≤ m := by
  by_contra hnm
  have hmn : m < n := Nat.lt_of_not_ge hnm
  let c : ℕ → Chain (cross m) := fun i => T (crossTower n i)
  have hstep : ∀ i < m, boundary (cross m) (c (i+1)) =
      normMap (cross m) flip (c i) := by
    intro i hi
    change boundary (cross m) (T (crossTower n (i+1))) =
      normMap (cross m) flip (T (crossTower n i))
    rw [← LinearMap.comp_apply, hd, LinearMap.comp_apply,
      crossTower_boundary n i (by omega), ← LinearMap.comp_apply, ← hN,
      LinearMap.comp_apply]
  have htop : c m = 0 := by
    have hg := hgrade (m+1) (crossTower_degree n m)
    change c m ∈ degreeChains (cross m) (m+1) at hg
    rw [degreeChains_eq_bot_of_card_bound (cross m) (m+1)
      (fun s hs => Nat.lt_succ_of_le (cross_card m s hs)), Submodule.mem_bot] at hg
    exact hg
  have hh := antipodal_tower_augmentation_zero (cross m) flip (cross_flip m)
    flip_involutive (cross_free m) m c hstep (by rw [htop, map_zero])
  change augmentation (cross m) (T (crossTower n 0)) = 0 at hh
  rw [← LinearMap.comp_apply, ha, crossTower_augmentation n (by omega)] at hh
  exact one_ne_zero hh

end BorsukNine.SimplicialChains

namespace BorsukNine.SimplicialChains
open Finset
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma barycenter_eq_centerMass (s : Finset E) :
    barycenter s = s.centerMass (fun _ => (1 : ℝ)) id := by
  simp [barycenter, Finset.centerMass]

lemma barycenter_mem_convex {A : Set E} (hA : Convex ℝ A) {s : Finset E}
    (hs : s.Nonempty) (hsA : (s : Set E) ⊆ A) : barycenter s ∈ A := by
  rw [barycenter_eq_centerMass]
  apply hA.centerMass_mem
  · intro x hx; exact zero_le_one
  · simpa using (Nat.cast_pos.mpr hs.card_pos : (0 : ℝ) < s.card)
  · intro x hx; exact hsA hx

lemma barycenter_norm_le {s : Finset E} (hs : s.Nonempty) {D : ℝ}
    (hD : ∀ x ∈ s, ‖x‖ ≤ D) : ‖barycenter s‖ ≤ D := by
  have h := barycenter_mem_convex (convex_closedBall (0 : E) D) hs (A := Metric.closedBall 0 D)
    (fun x hx => by simpa only [Metric.mem_closedBall, dist_zero_right] using hD x hx)
  simpa only [Metric.mem_closedBall, dist_zero_right] using h

lemma barycenter_inner {s : Finset E} (hs : s.Nonempty) (w : E)
    (hw : ∀ x ∈ s, ⟪w,x⟫ = 1) : ⟪w,barycenter s⟫ = 1 := by
  rw [barycenter, real_inner_smul_right, inner_sum]
  simp only [Finset.sum_congr rfl hw, Finset.sum_const, nsmul_eq_mul, mul_one]
  exact inv_mul_cancel₀ (by exact_mod_cast hs.card_ne_zero)

lemma barycenter_sub_eq {s : Finset E} (hs : s.Nonempty) (x : E) :
    barycenter s - x = (s.card : ℝ)⁻¹ • ∑ y ∈ s, (y-x) := by
  rw [Finset.sum_sub_distrib, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ]
  rw [smul_sub, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hs.card_ne_zero), one_smul]
  rfl

lemma barycenter_dist_vertex [DecidableEq E] {s : Finset E} {x : E} (hx : x ∈ s)
    {D : ℝ} (hD : ∀ y ∈ s, ∀ z ∈ s, dist y z ≤ D) :
    dist (barycenter s) x ≤ ((s.card : ℝ)-1) / s.card * D := by
  have hs : s.Nonempty := ⟨x,hx⟩
  have hc : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  rw [dist_eq_norm, barycenter_sub_eq hs x, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (le_of_lt hc))]
  have hh : (∑ y ∈ s, (y-x)) = ∑ y ∈ s.erase x, (y-x) := by
    rw [← Finset.sum_erase_add _ _ hx]
    simp
  rw [hh]
  calc
    (s.card : ℝ)⁻¹ * ‖∑ y ∈ s.erase x, (y-x)‖ ≤
        (s.card : ℝ)⁻¹ * ∑ y ∈ s.erase x, ‖y-x‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr (le_of_lt hc))
    _ ≤ (s.card : ℝ)⁻¹ * ∑ y ∈ s.erase x, D := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (le_of_lt hc))
      apply Finset.sum_le_sum
      intro y hy
      simpa only [dist_eq_norm] using hD y (Finset.mem_of_mem_erase hy) x hx
    _ = ((s.card : ℝ)-1) / s.card * D := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_erase_of_mem hx,
        Nat.cast_sub hs.card_pos, Nat.cast_one]
      ring

lemma barycenter_dist_carrier [DecidableEq E] {s t : Finset E} (ht : t.Nonempty)
    (hts : t ⊆ s) {D : ℝ} (hD : ∀ x ∈ s, ∀ y ∈ s, dist x y ≤ D) :
    dist (barycenter s) (barycenter t) ≤ ((s.card : ℝ)-1) / s.card * D := by
  have h := barycenter_mem_convex
    (convex_closedBall (barycenter s) (((s.card : ℝ)-1) / s.card * D)) ht
    (fun x hx => (Metric.mem_closedBall').mpr (barycenter_dist_vertex (hts hx) hD))
  exact (Metric.mem_closedBall').mp h

lemma barycenter_mesh_factor {a n : ℕ} (ha : 0 < a) (han : a ≤ n) :
    ((a : ℝ)-1) / a ≤ ((n : ℝ)-1) / n := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hn' : (0 : ℝ) < n := by exact_mod_cast lt_of_lt_of_le ha han
  apply (div_le_div_iff₀ ha' hn').mpr
  have han' : (a : ℝ) ≤ n := by exact_mod_cast han
  nlinarith

end BorsukNine.SimplicialChains

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Simplicial_BarycenterNeg
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [DecidableEq E]

lemma barycenter_neg (s : Finset E) : barycenter (s.image Neg.neg) = -barycenter s := by
  rw [barycenter, Finset.card_image_iff.mpr neg_injective.injOn,
    Finset.sum_image neg_injective.injOn, Finset.sum_neg_distrib,
    smul_neg, barycenter]

lemma hemisphere_neg (R : ℝ) (s : Finset E) :
    s ∈ hemisphereComplex R ↔ s.image Neg.neg ∈ hemisphereComplex R := by
  constructor
  · rintro ⟨hn,w,hw,hh⟩
    refine ⟨hn.image _, -w, by simpa using hw, ?_⟩
    intro x hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    simpa using hh y hy
  · rintro ⟨hn,w,hw,hh⟩
    refine ⟨Finset.image_nonempty.mp hn, -w, by simpa using hw, ?_⟩
    intro x hx
    have h := hh (-x) (Finset.mem_image_of_mem Neg.neg hx)
    simpa using h

omit [DecidableEq E] in
lemma hemisphere_subdivision_carrier (R : ℝ) :
    SubdivisionCarrier (hemisphereComplex R : PreAbstractSimplicialComplex E)
      (hemisphereComplex R) barycenter := by
  rintro s ⟨hn,w,hw,hh⟩ t ht hts
  refine ⟨ht,w,hw,?_⟩
  intro x hx
  obtain ⟨u,hu,hus,rfl⟩ := hts hx
  exact ⟨barycenter_norm_le hu (fun y hy => (hh y (hus hy)).1),
    barycenter_inner hu w (fun y hy => (hh y (hus hy)).2)⟩

lemma subdivSimplex_mesh (R : ℝ) (s : Finset E) (n : ℕ) (hsn : s.card ≤ n)
    (D : ℝ) (hD : 0 ≤ D) (hsD : ∀ x ∈ s, ∀ y ∈ s, dist x y ≤ D)
    {t : {s : Finset E // s ∈ hemisphereComplex R}}
    (ht : t ∈ (subdivSimplex (hemisphereComplex R) barycenter s).support) :
    ∀ x ∈ t.val, ∀ y ∈ t.val, dist x y ≤ ((n : ℝ)-1) / n * D := by
  induction s using Finset.strongInductionOn generalizing t with
  | _ s ih =>
    rcases s.eq_empty_or_nonempty with rfl | hn
    · simp at ht
    have hfac : 0 ≤ ((n : ℝ)-1) / n := by
      have hn' : (1 : ℝ) ≤ n := by exact_mod_cast le_trans hn.card_pos hsn
      exact div_nonneg (by linarith) (by positivity)
    by_cases hc : s.card = 1
    · rw [subdivSimplex_one _ _ hc, mem_support_simplex] at ht
      intro x hx y hy
      rw [ht, Finset.mem_singleton] at hx hy
      subst x; subst y
      simpa only [dist_self] using mul_nonneg hfac hD
    · rw [subdivSimplex_many _ _ hn hc] at ht
      obtain ⟨u,hu,_,htu⟩ := support_cone _ (barycenter s) _ ht
      obtain ⟨a,ha,hua⟩ := support_sum_chains _ s _ hu
      have hsmall := ih (s.erase a) (Finset.erase_ssubset ha)
        (le_trans (Finset.card_le_card (Finset.erase_subset a s)) hsn)
        (fun x hx y hy => hsD x (Finset.mem_of_mem_erase hx) y (Finset.mem_of_mem_erase hy)) hua
      have hcarrier := (subdivSimplex_carrier _ barycenter _ hua).trans
        (vertexCarrier_mono barycenter (Finset.erase_subset a s))
      have hcenter (x : E) (hx : x ∈ u.val) :
          dist (barycenter s) x ≤ ((n : ℝ)-1) / n * D := by
        obtain ⟨v,hv,hvs,rfl⟩ := hcarrier hx
        exact (barycenter_dist_carrier hv hvs hsD).trans
          (mul_le_mul_of_nonneg_right (barycenter_mesh_factor hn.card_pos hsn) hD)
      intro x hx y hy
      rw [htu, Finset.mem_insert] at hx hy
      rcases hx with rfl | hx <;> rcases hy with rfl | hy
      · simpa only [dist_self] using mul_nonneg hfac hD
      · exact hcenter y hy
      · rw [dist_comm]; exact hcenter x hx
      · exact hsmall x hx y hy

end BorsukNine.SimplicialChains

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Simplicial_MapChainsEquivSimplexAll
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset
variable {V W U : Type*} [DecidableEq V] [DecidableEq W] [DecidableEq U]

omit [DecidableEq W] [DecidableEq U] in
lemma mapChains_equiv_simplex_all (K : PreAbstractSimplicialComplex V) (e : V ≃ V)
    (he : ∀ s, s ∈ K ↔ s.image e ∈ K) (s : Finset V) :
    mapChains K K e (simplex K s) = simplex K (s.image e) := by
  classical
  by_cases hs : s ∈ K
  · rw [mapChains_simplex K K e hs, mapSimplex,
      ite_eq_left (Finset.card_image_iff.mpr e.injective.injOn)]
  · have ht : s.image e ∉ K := (he s).not.mp hs
    simp [simplex, hs, ht]

omit [DecidableEq W] [DecidableEq U] in
lemma cone_equivariant (K : PreAbstractSimplicialComplex V) (e : V ≃ V)
    (he : ∀ s, s ∈ K ↔ s.image e ∈ K) (a : V) :
    (mapChains K K e).comp (cone K a) = (cone K (e a)).comp (mapChains K K e) := by
  apply Finsupp.lhom_ext
  intro s r
  have hm := mapChains_equiv_simplex_all K e he s.val
  have hc := cone_simplex K a s.property
  have hsc := cone_simplex K (e a) ((he s.val).mp s.property)
  have hh : mapChains K K e (cone K a (simplex K s.val)) =
      cone K (e a) (mapChains K K e (simplex K s.val)) := by
    rw [hc, hm, hsc]
    by_cases ha : a ∈ s.val
    · rw [ite_eq_left ha, ite_eq_left (Finset.mem_image_of_mem e ha), map_zero]
    · have hna : e a ∉ s.val.image e := by
        intro h
        obtain ⟨b, hb, heq⟩ := Finset.mem_image.mp h
        exact ha (e.injective heq ▸ hb)
      rw [ite_eq_right ha, ite_eq_right hna, mapChains_equiv_simplex_all K e he,
        Finset.image_insert]
  rw [simplex_of_mem K s.property] at hh
  have hr : Finsupp.single s r = r • Finsupp.single s (1 : F₂) := by simp
  simp only [LinearMap.comp_apply, hr, map_smul, hh]

omit [DecidableEq U] in
lemma subdivSimplex_equivariant (L : PreAbstractSimplicialComplex W)
    (e : V ≃ V) (d : W ≃ W) (hd : ∀ s, s ∈ L ↔ s.image d ∈ L)
    (b : Finset V → W) (hb : ∀ s, b (s.image e) = d (b s)) (s : Finset V) :
    mapChains L L d (subdivSimplex L b s) = subdivSimplex L b (s.image e) := by
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    rcases s.eq_empty_or_nonempty with rfl | hn
    · simp
    have hc : (s.image e).card = s.card := Finset.card_image_iff.mpr e.injective.injOn
    by_cases hs : s.card = 1
    · rw [subdivSimplex_one L b hs, subdivSimplex_one L b (hc.trans hs),
        mapChains_equiv_simplex_all L d hd, Finset.image_singleton, hb]
    · rw [subdivSimplex_many L b hn hs,
        subdivSimplex_many L b (hn.image e) (by omega)]
      have hcone := LinearMap.congr_fun (cone_equivariant L d hd (b s))
        (∑ a ∈ s, subdivSimplex L b (s.erase a))
      rw [LinearMap.comp_apply, LinearMap.comp_apply] at hcone
      rw [hcone, map_sum, hb, Finset.sum_image (fun a _ b _ he => e.injective he)]
      apply congrArg (cone L (d (b s)))
      apply Finset.sum_congr rfl
      intro a ha
      rw [ih (s.erase a) (Finset.erase_ssubset ha), image_erase_of_injOn e s e.injective.injOn ha]

omit [DecidableEq U] in
lemma subdivMap_equivariant (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (e : V ≃ V) (d : W ≃ W)
    (he : ∀ s, s ∈ K ↔ s.image e ∈ K) (hd : ∀ s, s ∈ L ↔ s.image d ∈ L)
    (b : Finset V → W) (hb : ∀ s, b (s.image e) = d (b s)) :
    (mapChains L L d).comp (subdivMap K L b) =
      (subdivMap K L b).comp (mapChains K K e) := by
  apply Finsupp.lhom_ext
  intro s r
  have hh : mapChains L L d (subdivMap K L b (simplex K s.val)) =
      subdivMap K L b (mapChains K K e (simplex K s.val)) := by
    rw [subdivMap_simplex K L b s.property, subdivSimplex_equivariant L e d hd b hb,
      mapChains_equiv_simplex_all K e he, subdivMap_simplex K L b ((he s.val).mp s.property)]
  rw [simplex_of_mem K s.property] at hh
  have hr : Finsupp.single s r = r • Finsupp.single s (1 : F₂) := by simp
  simp only [LinearMap.comp_apply, hr, map_smul, hh]

omit [DecidableEq U] in
lemma subdivMap_norm (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (e : V ≃ V) (d : W ≃ W)
    (he : ∀ s, s ∈ K ↔ s.image e ∈ K) (hd : ∀ s, s ∈ L ↔ s.image d ∈ L)
    (b : Finset V → W) (hb : ∀ s, b (s.image e) = d (b s)) :
    (normMap L d).comp (subdivMap K L b) =
      (subdivMap K L b).comp (normMap K e) := by
  simp only [normMap, LinearMap.add_comp, LinearMap.comp_add, LinearMap.id_comp,
    LinearMap.comp_id, subdivMap_equivariant K L e d he hd b hb]

omit [DecidableEq U] in
lemma subdivMap_degree (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (b : Finset V → W) (d : ℕ) :
    degreeChains K d ≤ (degreeChains L d).comap (subdivMap K L b) := by
  apply grade_map K L _ d d
  intro s hs hsd
  rw [subdivMap_simplex K L b hs, ← hsd]
  exact subdivSimplex_degree L b s

end BorsukNine.SimplicialChains

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Simplicial_LinearMapSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset
variable {V W : Type*} [DecidableEq V] [DecidableEq W]

omit [DecidableEq V] in
lemma linearMap_eq_of_support {K : PreAbstractSimplicialComplex V}
    {M : Type*} [AddCommMonoid M] [Module F₂ M]
    (T U : Chain K →ₗ[F₂] M) (c : Chain K)
    (hc : ∀ s ∈ c.support, T (simplex K s.val) = U (simplex K s.val)) : T c = U c := by
  rw [chain_eq_sum K c, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro s hs
  rw [map_smul, map_smul, hc s hs]

lemma mapChains_boundary_simplex_of_image (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (f : V → W)
    {s : Finset V} (hs : s ∈ K) (ht : s.image f ∈ L) :
    boundary L (mapChains K L f (simplex K s)) =
      mapChains K L f (boundary K (simplex K s)) := by
  rw [mapChains_simplex K L f hs, boundary_simplex K hs, map_sum]
  have h (a : V) : mapChains K L f (simplex K (s.erase a)) = mapSimplex L f (s.erase a) :=
    mapChains_simplex_subset K L f hs (Finset.erase_subset a s)
  simp_rw [h]
  by_cases hinj : Set.InjOn f s
  · rw [mapSimplex, ite_eq_left (Finset.card_image_iff.mpr hinj), boundary_simplex L ht]
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro a ha
      have hj : Set.InjOn f (s.erase a) := hinj.mono (Finset.erase_subset a s)
      rw [mapSimplex, ite_eq_left (Finset.card_image_iff.mpr hj), image_erase_of_injOn f s hinj ha]
    · exact hinj
  · rw [mapSimplex, ite_eq_right (mt Finset.card_image_iff.mp hinj), map_zero,
      mapSimplex_boundary_degenerate L f s hinj]

lemma mapChains_boundary_of_support (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (f : V → W) (c : Chain K)
    (hc : ∀ s ∈ c.support, s.val.image f ∈ L) :
    boundary L (mapChains K L f c) = mapChains K L f (boundary K c) := by
  apply linearMap_eq_of_support ((boundary L).comp (mapChains K L f))
    ((mapChains K L f).comp (boundary K)) c
  intro s hs
  exact mapChains_boundary_simplex_of_image K L f s.property (hc s hs)

omit [DecidableEq V] in
lemma mapChains_augmentation_simplex_of_image (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (f : V → W)
    {s : Finset V} (hs : s ∈ K) (ht : s.image f ∈ L) :
    augmentation L (mapChains K L f (simplex K s)) = augmentation K (simplex K s) := by
  rw [mapChains_simplex K L f hs, augmentation_simplex K hs]
  by_cases hcard : (s.image f).card = s.card
  · rw [mapSimplex, ite_eq_left hcard, augmentation_simplex L ht, hcard]
  · have hne : s.card ≠ 1 := by
      intro hc
      obtain ⟨v,rfl⟩ := Finset.card_eq_one.mp hc
      simp at hcard
    simp [mapSimplex, hcard, hne]

omit [DecidableEq V] in
lemma mapChains_augmentation_of_support (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (f : V → W) (c : Chain K)
    (hc : ∀ s ∈ c.support, s.val.image f ∈ L) :
    augmentation L (mapChains K L f c) = augmentation K c := by
  apply linearMap_eq_of_support ((augmentation L).comp (mapChains K L f)) (augmentation K) c
  intro s hs
  exact mapChains_augmentation_simplex_of_image K L f s.property (hc s hs)

omit [DecidableEq V] in
lemma mapChains_degree_all (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (f : V → W) (d : ℕ) :
    degreeChains K d ≤ (degreeChains L d).comap (mapChains K L f) := by
  apply grade_map K L _ d d
  intro s hs hd
  rw [mapChains_simplex K L f hs, mapSimplex]
  split_ifs with hh
  · rw [← hd, ← hh]
    exact simplex_mem_degree_all L _
  · exact Submodule.zero_mem _

lemma mapChains_equivariant (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (e : V ≃ V) (d : W ≃ W)
    (he : ∀ s, s ∈ K ↔ s.image e ∈ K) (hd : ∀ s, s ∈ L ↔ s.image d ∈ L)
    (f : V → W) (hf : ∀ s ∈ K, ∀ x ∈ s, f (e x) = d (f x)) :
    (mapChains L L d).comp (mapChains K L f) =
      (mapChains K L f).comp (mapChains K K e) := by
  apply Finsupp.lhom_ext
  intro s r
  have him : (s.val.image e).image f = (s.val.image f).image d := by
    simp only [Finset.image_image]
    exact Finset.image_congr (fun x hx => hf s.val s.property x hx)
  have hcard : (s.val.image e).card = s.val.card := Finset.card_image_iff.mpr e.injective.injOn
  have hcard' : ((s.val.image f).image d).card = (s.val.image f).card :=
    Finset.card_image_iff.mpr d.injective.injOn
  have hh : mapChains L L d (mapChains K L f (simplex K s.val)) =
      mapChains K L f (mapChains K K e (simplex K s.val)) := by
    rw [mapChains_simplex K L f s.property, mapChains_equiv_simplex_all K e he,
      mapChains_simplex K L f ((he s.val).mp s.property)]
    simp only [mapSimplex, him, hcard, hcard']
    split_ifs
    · exact mapChains_equiv_simplex_all L d hd _
    · exact map_zero _
  rw [simplex_of_mem K s.property] at hh
  have hr : Finsupp.single s r = r • Finsupp.single s (1 : F₂) := by simp
  simp only [LinearMap.comp_apply, hr, map_smul, hh]

lemma mapChains_norm (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (e : V ≃ V) (d : W ≃ W)
    (he : ∀ s, s ∈ K ↔ s.image e ∈ K) (hd : ∀ s, s ∈ L ↔ s.image d ∈ L)
    (f : V → W) (hf : ∀ s ∈ K, ∀ x ∈ s, f (e x) = d (f x)) :
    (normMap L d).comp (mapChains K L f) =
      (mapChains K L f).comp (normMap K e) := by
  simp only [normMap, LinearMap.add_comp, LinearMap.comp_add, LinearMap.id_comp,
    LinearMap.comp_id, mapChains_equivariant K L e d he hd f hf]

end BorsukNine.SimplicialChains

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Simplicial_CrossEmbedding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset
open scoped RealInnerProductSpace

lemma crossEmbedding_norm (n : ℕ) (v : SignedVertex) (hv : v.1 < n) :
    ‖crossEmbedding n v‖ = 1 := by
  simp only [crossEmbedding, dite_eq_left hv, norm_smul, PiLp.norm_single]
  cases v.2 <;> norm_num

lemma crossEmbedding_flip (n : ℕ) (v : SignedVertex) :
    crossEmbedding n (flip v) = -crossEmbedding n v := by
  rcases v with ⟨i,b⟩
  cases b <;> simp only [crossEmbedding, flip_apply] <;> split_ifs <;> simp_all

lemma crossEmbedding_inner_ne (n : ℕ) {v w : SignedVertex}
    (hvw : v.1 ≠ w.1) : ⟪crossEmbedding n v, crossEmbedding n w⟫ = 0 := by
  unfold crossEmbedding
  split_ifs <;> simp_all [EuclideanSpace.inner_single_left]

lemma crossEmbedding_inner_self (n : ℕ) (v : SignedVertex) (hv : v.1 < n) :
    ⟪crossEmbedding n v, crossEmbedding n v⟫ = 1 := by
  rw [real_inner_self_eq_norm_sq, crossEmbedding_norm n v hv]
  norm_num

lemma crossEmbedding_face (n : ℕ) (s : Finset SignedVertex) (hs : s ∈ cross n) :
    s.image (crossEmbedding n) ∈ hemisphereComplex (n:ℝ) := by
  refine ⟨hs.1.image _, ∑ v ∈ s, crossEmbedding n v, ?_, ?_⟩
  · calc
      ‖∑ v ∈ s, crossEmbedding n v‖ ≤ ∑ v ∈ s, ‖crossEmbedding n v‖ := norm_sum_le _ _
      _ = s.card := by simp only [Finset.sum_congr rfl (fun v hv => crossEmbedding_norm n v (hs.2.1 v hv)), Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ (n:ℝ) := by exact_mod_cast cross_card n s hs
  · intro x hx
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hx
    refine ⟨le_of_eq (crossEmbedding_norm n v (hs.2.1 v hv)), ?_⟩
    rw [sum_inner, Finset.sum_eq_single v]
    · exact crossEmbedding_inner_self n v (hs.2.1 v hv)
    · intro w hw hwv
      exact crossEmbedding_inner_ne n (fun he => hwv (hs.2.2 hw hv he))
    · exact fun hn => False.elim (hn hv)

lemma crossGeometricMap_boundary (n : ℕ) :
    (boundary (hemisphereComplex (n:ℝ))).comp (crossGeometricMap n) =
      (crossGeometricMap n).comp (boundary (cross n)) :=
  mapChains_boundary _ _ _ (crossEmbedding_face n)

lemma crossGeometricMap_augmentation (n : ℕ) :
    (augmentation (hemisphereComplex (n:ℝ))).comp (crossGeometricMap n) =
      augmentation (cross n) := mapChains_augmentation _ _ _ (crossEmbedding_face n)

lemma crossGeometricMap_degree (n d : ℕ) :
    degreeChains (cross n) d ≤ (degreeChains (hemisphereComplex (n:ℝ)) d).comap
      (crossGeometricMap n) := mapChains_degree _ _ _ (crossEmbedding_face n) d

lemma crossGeometricMap_norm (n : ℕ) :
    (normMap (hemisphereComplex (n:ℝ)) (Equiv.neg _)).comp (crossGeometricMap n) =
      (crossGeometricMap n).comp (normMap (cross n) flip) := by
  apply mapChains_norm _ _ flip (Equiv.neg _) (cross_flip n) (hemisphere_neg (n:ℝ))
  intro s hs x hx
  exact crossEmbedding_flip n x

end BorsukNine.SimplicialChains

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Simplicial_MaxIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset

lemma maxIndex_le {m : ℕ} [NeZero m] (g : Fin m → ℝ) (i : Fin m) :
    g i ≤ g (maxIndex g) :=
  (Finset.exists_max_image Finset.univ g Finset.univ_nonempty).choose_spec.2 i (Finset.mem_univ _)

lemma peakIndex_neg {m : ℕ} [NeZero m] (y : EuclideanSpace ℝ (Fin m)) :
    peakIndex (-y) = peakIndex y := by
  unfold peakIndex
  congr 1
  ext i
  simp

lemma euclidean_norm_le_sum_abs {m : ℕ} (y : EuclideanSpace ℝ (Fin m)) :
    ‖y‖ ≤ ∑ i, |y i| := by
  have hy : y = ∑ i, EuclideanSpace.single i (y i) := by
    ext i
    simp
  calc
    ‖y‖ = ‖∑ i, EuclideanSpace.single i (y i)‖ := congrArg norm hy
    _ ≤ ∑ i, ‖EuclideanSpace.single i (y i)‖ := norm_sum_le _ _
    _ = ∑ i, |y i| := by simp

lemma peak_large {m : ℕ} [NeZero m] (y : EuclideanSpace ℝ (Fin m)) (hy : ‖y‖ = 1) :
    (1:ℝ) / m ≤ |y (peakIndex y)| := by
  have h := euclidean_norm_le_sum_abs y
  rw [hy] at h
  have hsum : ∑ i : Fin m, |y i| ≤ (m:ℝ) * |y (peakIndex y)| := by
    calc
      ∑ i : Fin m, |y i| ≤ ∑ _ : Fin m, |y (peakIndex y)| :=
        Finset.sum_le_sum (fun i _ => maxIndex_le (fun j => |y j|) i)
      _ = _ := by simp
  exact (div_le_iff₀ (by exact_mod_cast NeZero.pos m)).mpr (by nlinarith)

lemma sphereLabel_bound {m : ℕ} [NeZero m] (y : EuclideanSpace ℝ (Fin m)) :
    (sphereLabel y).1 < m := (peakIndex y).isLt

lemma sphereLabel_neg {m : ℕ} [NeZero m] (y : EuclideanSpace ℝ (Fin m)) (hy : ‖y‖ = 1) :
    sphereLabel (-y) = flip (sphereLabel y) := by
  have hpeak : y (peakIndex y) ≠ 0 := by
    have h := peak_large y hy
    have hm : (0:ℝ) < (1:ℝ)/m := div_pos zero_lt_one (by exact_mod_cast NeZero.pos m)
    intro he
    rw [he, abs_zero] at h
    linarith
  apply Prod.ext
  · simp only [sphereLabel, peakIndex_neg, flip_apply]
  · simp only [sphereLabel, peakIndex_neg, flip_apply, PiLp.neg_apply]
    by_cases h : y (peakIndex y) < 0
    · have h' : ¬ -y (peakIndex y) < 0 := by linarith
      simp [h,h']
    · have h' : -y (peakIndex y) < 0 := by rcases lt_or_gt_of_ne hpeak with hn | hp <;> linarith
      simp [h,h']

lemma sphereLabel_compatible {m : ℕ} [NeZero m]
    (y z : EuclideanSpace ℝ (Fin m)) (hy : ‖y‖ = 1) (hz : ‖z‖ = 1)
    (hd : dist y z < (1:ℝ)/m) (hi : (sphereLabel y).1 = (sphereLabel z).1) :
    sphereLabel y = sphereLabel z := by
  have he : peakIndex y = peakIndex z := Fin.ext hi
  have hcoord : |y (peakIndex y) - z (peakIndex y)| ≤ dist y z := by
    simpa only [Real.dist_eq] using PiLp.dist_apply_le y z (peakIndex y)
  have hym := peak_large y hy
  have hzm := peak_large z hz
  rw [← he] at hzm
  apply Prod.ext hi
  change decide (y (peakIndex y) < 0) = decide (z (peakIndex z) < 0)
  rw [← he]
  congr 1
  apply propext
  constructor
  · intro hyneg
    by_contra hzneg
    have hzpos := le_of_not_gt hzneg
    rw [abs_of_neg hyneg] at hym
    rw [abs_of_nonpos (by linarith)] at hcoord
    linarith
  · intro hzneg
    by_contra hyneg
    have hypos := le_of_not_gt hyneg
    rw [abs_of_neg hzneg] at hzm
    rw [abs_of_nonneg (by linarith)] at hcoord
    linarith

end BorsukNine.SimplicialChains

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Simplicial_Refinement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [DecidableEq E]

lemma refinement_boundary (R : ℝ) (r : ℕ) :
    (boundary (hemisphereComplex R : PreAbstractSimplicialComplex E)).comp (refinement R r) =
      (refinement R r).comp (boundary (hemisphereComplex R)) := by
  induction r with
  | zero => simp only [refinement, LinearMap.comp_id, LinearMap.id_comp]
  | succ r ih =>
    rw [refinement, ← LinearMap.comp_assoc, subdivMap_boundary _ _ _ (hemisphere_subdivision_carrier R),
      LinearMap.comp_assoc, ih, ← LinearMap.comp_assoc]

lemma refinement_augmentation (R : ℝ) (r : ℕ) :
    (augmentation (hemisphereComplex R : PreAbstractSimplicialComplex E)).comp
      (refinement R r) = augmentation (hemisphereComplex R) := by
  induction r with
  | zero => simp only [refinement, LinearMap.comp_id]
  | succ r ih =>
    rw [refinement, ← LinearMap.comp_assoc,
      subdivMap_augmentation _ _ _ (hemisphere_subdivision_carrier R), ih]

lemma refinement_norm (R : ℝ) (r : ℕ) :
    (normMap (hemisphereComplex R : PreAbstractSimplicialComplex E) (Equiv.neg E)).comp
      (refinement R r) = (refinement R r).comp (normMap (hemisphereComplex R) (Equiv.neg E)) := by
  induction r with
  | zero => simp only [refinement, LinearMap.comp_id, LinearMap.id_comp]
  | succ r ih =>
    rw [refinement, ← LinearMap.comp_assoc,
      subdivMap_norm _ _ (Equiv.neg E) (Equiv.neg E) (hemisphere_neg R) (hemisphere_neg R)
        barycenter (barycenter_neg), LinearMap.comp_assoc, ih, ← LinearMap.comp_assoc]

lemma refinement_degree (R : ℝ) (r d : ℕ) :
    degreeChains (hemisphereComplex R : PreAbstractSimplicialComplex E) d ≤
      (degreeChains (hemisphereComplex R) d).comap (refinement R r) := by
  induction r with
  | zero => intro c hc; exact hc
  | succ r ih =>
    intro c hc
    change subdivMap (hemisphereComplex R) (hemisphereComplex R) barycenter
      (refinement R r c) ∈ degreeChains (hemisphereComplex R) d
    exact subdivMap_degree (hemisphereComplex R : PreAbstractSimplicialComplex E)
      (hemisphereComplex R) barycenter d (ih hc)

lemma refinement_mesh (R : ℝ) (r n : ℕ) {c : Chain (hemisphereComplex R : PreAbstractSimplicialComplex E)}
    (hc : c ∈ degreeChains (hemisphereComplex R) n) {D : ℝ} (hD : 0 ≤ D)
    (hmesh : ∀ s ∈ c.support, ∀ x ∈ s.val, ∀ y ∈ s.val, dist x y ≤ D)
    {t : {s : Finset E // s ∈ hemisphereComplex R}}
    (ht : t ∈ (refinement R r c).support) :
    ∀ x ∈ t.val, ∀ y ∈ t.val, dist x y ≤ (((n:ℝ)-1)/n)^r * D := by
  induction r generalizing t with
  | zero => simpa only [refinement, LinearMap.id_apply, pow_zero, one_mul] using hmesh t ht
  | succ r ih =>
    change t ∈ (subdivMap (hemisphereComplex R) (hemisphereComplex R) barycenter
      (refinement R r c)).support at ht
    obtain ⟨s,hs,hts⟩ := support_linearMap _ _ _ _ ht
    rw [subdivMap_simplex _ _ _ s.property] at hts
    have hdeg := refinement_degree R r n hc hs
    change s.val.card = n at hdeg
    have hn : 0 < n := hdeg ▸ s.property.1.card_pos
    have hfac : 0 ≤ ((n:ℝ)-1)/n := by
      have hh : (1:ℝ) ≤ n := by exact_mod_cast hn
      exact div_nonneg (by linarith) (by positivity)
    have hh := subdivSimplex_mesh R s.val n (le_of_eq hdeg)
      ((((n:ℝ)-1)/n)^r * D) (mul_nonneg (pow_nonneg hfac _) hD) (ih hs) hts
    simpa only [pow_succ', mul_assoc] using hh

omit [DecidableEq E] in
lemma hemisphere_mesh_two (R : ℝ) {s : Finset E} (hs : s ∈ hemisphereComplex R)
    {x y : E} (hx : x ∈ s) (hy : y ∈ s) : dist x y ≤ 2 := by
  obtain ⟨_, _, _, unit_norm⟩ := hs
  calc
    dist x y ≤ ‖x‖ + ‖y‖ := dist_le_norm_add_norm x y
    _ ≤ 2 := by linarith [(unit_norm x hx).1, (unit_norm y hy).1]

lemma refinement_mesh_uniform (R : ℝ) (r n d : ℕ) (hd : d ≤ n)
    {c : Chain (hemisphereComplex R : PreAbstractSimplicialComplex E)}
    (hc : c ∈ degreeChains (hemisphereComplex R) d)
    {t : {s : Finset E // s ∈ hemisphereComplex R}}
    (ht : t ∈ (refinement R r c).support) :
    ∀ x ∈ t.val, ∀ y ∈ t.val, dist x y ≤ (((n:ℝ)-1)/n)^r * 2 := by
  have hdeg := refinement_degree R r d hc ht
  have htpos := t.property.1.card_pos
  change t.val.card = d at hdeg
  have hdpos : 0 < d := hdeg ▸ htpos
  have hfac : 0 ≤ ((d:ℝ)-1)/d := by
    have hh : (1:ℝ) ≤ d := by exact_mod_cast hdpos
    exact div_nonneg (by linarith) (by positivity)
  have hm := refinement_mesh R r d hc (D := 2) (by norm_num)
    (fun simplex _ _ first_mem _ second_mem =>
      hemisphere_mesh_two R simplex.property first_mem second_mem) ht
  intro x hx y hy
  exact (hm x hx y hy).trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ hfac (barycenter_mesh_factor hdpos hd) r) (by norm_num))

end BorsukNine.SimplicialChains

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Simplicial_FineCrossMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset
open scoped RealInnerProductSpace

lemma fineCrossMap_boundary (n r : ℕ) :
    (boundary (hemisphereComplex (n:ℝ))).comp (fineCrossMap n r) =
      (fineCrossMap n r).comp (boundary (cross n)) := by
  rw [fineCrossMap, ← LinearMap.comp_assoc, refinement_boundary,
    LinearMap.comp_assoc, crossGeometricMap_boundary, ← LinearMap.comp_assoc]

lemma fineCrossMap_augmentation (n r : ℕ) :
    (augmentation (hemisphereComplex (n:ℝ))).comp (fineCrossMap n r) = augmentation (cross n) := by
  rw [fineCrossMap, ← LinearMap.comp_assoc, refinement_augmentation,
    crossGeometricMap_augmentation]

lemma fineCrossMap_norm (n r : ℕ) :
    (normMap (hemisphereComplex (n:ℝ)) (Equiv.neg _)).comp (fineCrossMap n r) =
      (fineCrossMap n r).comp (normMap (cross n) flip) := by
  rw [fineCrossMap, ← LinearMap.comp_assoc, refinement_norm,
    LinearMap.comp_assoc, crossGeometricMap_norm, ← LinearMap.comp_assoc]

lemma fineCrossMap_degree (n r d : ℕ) :
    degreeChains (cross n) d ≤ (degreeChains (hemisphereComplex (n:ℝ)) d).comap
      (fineCrossMap n r) := by
  intro c hc
  change refinement (n:ℝ) r (crossGeometricMap n c) ∈ degreeChains (hemisphereComplex (n:ℝ)) d
  exact refinement_degree (E := EuclideanSpace ℝ (Fin n)) (n:ℝ) r d
    (crossGeometricMap_degree n d hc)

lemma fineCrossMap_simplex_mesh (n r : ℕ) {s : Finset SignedVertex} (hs : s ∈ cross n)
    {t : {s : Finset (EuclideanSpace ℝ (Fin n)) // s ∈ hemisphereComplex (n:ℝ)}}
    (ht : t ∈ (fineCrossMap n r (simplex (cross n) s)).support) :
    ∀ x ∈ t.val, ∀ y ∈ t.val, dist x y ≤ (((n:ℝ)-1)/n)^r * 2 := by
  apply refinement_mesh_uniform (n:ℝ) r n s.card (cross_card n s hs)
    (crossGeometricMap_degree n s.card (simplex_mem_degree _ hs)) ht

lemma annulus_compact (n : ℕ) : IsCompact (annulus n) := by
  apply (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) 1).of_isClosed_subset
  · exact (isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const)
  · intro x hx
    simpa only [Metric.mem_closedBall, dist_zero_right] using hx.2

lemma hemisphere_vertex_annulus (n : ℕ) (hn : 0 < n)
    {s : Finset (EuclideanSpace ℝ (Fin n))} (hs : s ∈ hemisphereComplex (n:ℝ))
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ s) : x ∈ annulus n := by
  obtain ⟨_,w,hw,hh⟩ := hs
  refine ⟨?_,(hh x hx).1⟩
  apply (div_le_iff₀ (by exact_mod_cast hn)).mpr
  have h := real_inner_le_norm w x
  rw [(hh x hx).2] at h
  calc
    1 ≤ ‖w‖ * ‖x‖ := h
    _ ≤ (n:ℝ) * ‖x‖ := mul_le_mul_of_nonneg_right hw (norm_nonneg x)
    _ = ‖x‖ * (n:ℝ) := mul_comm _ _

lemma annular_odd_dimension_bound (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (hg : ContinuousOn g (annulus n)) (hgn : ∀ x ∈ annulus n, ‖g x‖ = 1)
    (hgo : ∀ x ∈ annulus n, g (-x) = -g x) : n ≤ m := by
  classical
  let : NeZero m := ⟨by omega⟩
  have hunif := (annulus_compact n).uniformContinuousOn_of_continuous hg
  obtain ⟨δ,hδ,hclose⟩ := Metric.uniformContinuousOn_iff.mp hunif ((1:ℝ)/m)
    (div_pos zero_lt_one (by exact_mod_cast hm))
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hq : ((n:ℝ)-1)/n < 1 := (div_lt_one hn').mpr (by linarith)
  obtain ⟨r,hr⟩ := exists_pow_lt_of_lt_one (show (0:ℝ) < δ/2 by linarith) hq
  have hmeshδ : (((n:ℝ)-1)/n)^r * 2 < δ := by linarith
  let K : PreAbstractSimplicialComplex (EuclideanSpace ℝ (Fin n)) := hemisphereComplex (n:ℝ)
  let f : EuclideanSpace ℝ (Fin n) → SignedVertex := fun x => sphereLabel (g x)
  let U : Chain K →ₗ[F₂] Chain (cross m) := mapChains K (cross m) f
  let T : Chain (cross n) →ₗ[F₂] Chain (cross m) := U.comp (fineCrossMap n r)
  have hfine (s : Finset SignedVertex) (hs : s ∈ cross n)
      (t : {s : Finset (EuclideanSpace ℝ (Fin n)) // s ∈ K})
      (ht : t ∈ (fineCrossMap n r (simplex (cross n) s)).support) : t.val.image f ∈ cross m := by
    refine ⟨t.property.1.image _, ?_, ?_⟩
    · intro v hv
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hv
      exact sphereLabel_bound (g x)
    · intro v hv w hw he
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hw
      have hxa := hemisphere_vertex_annulus n hn t.property hx
      have hya := hemisphere_vertex_annulus n hn t.property hy
      apply sphereLabel_compatible (g x) (g y) (hgn x hxa) (hgn y hya) _ he
      exact hclose x hxa y hya ((fineCrossMap_simplex_mesh n r hs ht x hx y hy).trans_lt hmeshδ)
  have hdb : (boundary (cross m)).comp T = T.comp (boundary (cross n)) := by
    apply Finsupp.lhom_ext
    intro s a
    have hh : boundary (cross m) (T (simplex (cross n) s.val)) =
        T (boundary (cross n) (simplex (cross n) s.val)) := by
      change boundary (cross m) (mapChains K (cross m) f
        (fineCrossMap n r (simplex (cross n) s.val))) = _
      rw [mapChains_boundary_of_support K (cross m) f _ (hfine s.val s.property)]
      have hb := LinearMap.congr_fun (fineCrossMap_boundary n r) (simplex (cross n) s.val)
      rw [LinearMap.comp_apply, LinearMap.comp_apply] at hb
      rw [hb]
      rfl
    rw [simplex_of_mem (cross n) s.property] at hh
    have ha : Finsupp.single s a = a • Finsupp.single s (1:F₂) := by simp
    simp only [LinearMap.comp_apply, ha, map_smul, hh]
  have haug : (augmentation (cross m)).comp T = augmentation (cross n) := by
    apply Finsupp.lhom_ext
    intro s a
    have hh : augmentation (cross m) (T (simplex (cross n) s.val)) =
        augmentation (cross n) (simplex (cross n) s.val) := by
      change augmentation (cross m) (mapChains K (cross m) f
        (fineCrossMap n r (simplex (cross n) s.val))) = _
      rw [mapChains_augmentation_of_support K (cross m) f _ (hfine s.val s.property)]
      exact LinearMap.congr_fun (fineCrossMap_augmentation n r) _
    rw [simplex_of_mem (cross n) s.property] at hh
    have ha : Finsupp.single s a = a • Finsupp.single s (1:F₂) := by simp
    simp only [LinearMap.comp_apply, ha, map_smul, hh]
  have hnorm : (normMap (cross m) flip).comp T = T.comp (normMap (cross n) flip) := by
    have hu : (normMap (cross m) flip).comp U = U.comp (normMap K (Equiv.neg _)) := by
      apply mapChains_norm K (cross m) (Equiv.neg _) flip
        (hemisphere_neg (n:ℝ)) (cross_flip m) f
      intro s hs x hx
      have hxa := hemisphere_vertex_annulus n hn hs hx
      change sphereLabel (g (-x)) = flip (sphereLabel (g x))
      rw [hgo x hxa, sphereLabel_neg _ (hgn x hxa)]
    change (normMap (cross m) flip).comp (U.comp (fineCrossMap n r)) =
      (U.comp (fineCrossMap n r)).comp (normMap (cross n) flip)
    rw [← LinearMap.comp_assoc, hu, LinearMap.comp_assoc,
      fineCrossMap_norm, ← LinearMap.comp_assoc]
  apply cross_chain_dimension_bound n m T hdb hnorm haug
  intro d c hc
  change mapChains K (cross m) f (fineCrossMap n r c) ∈ degreeChains (cross m) d
  exact mapChains_degree_all K (cross m) f d (fineCrossMap_degree n r d hc)

end BorsukNine.SimplicialChains

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

lemma unitRadial_neg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (x : E) :
    unitRadial (-x) = -unitRadial x := by simp [unitRadial]

lemma unitRadial_continuousOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set E} (hS : ∀ x ∈ S, x ≠ 0) : ContinuousOn unitRadial S := by
  exact (continuous_norm.continuousOn.inv₀ (fun x hx => norm_ne_zero_iff.mpr (hS x hx))).smul
    continuous_id.continuousOn

lemma odd_sphere_dimension_bound (n m : ℕ) (hn : 0 < n)
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (hf : ContinuousOn f {x | ‖x‖ = 1}) (hfn : ∀ x, ‖x‖ = 1 → ‖f x‖ = 1)
    (hfo : ∀ x, ‖x‖ = 1 → f (-x) = -f x) : n ≤ m := by
  by_cases hm : 0 < m
  · have ha : ∀ x ∈ annulus n, x ≠ 0 := by
      intro x hx hzero
      have hn' : (0:ℝ) < n := by exact_mod_cast hn
      have hp : (0:ℝ) < 1/(n:ℝ) := div_pos zero_lt_one hn'
      simp only [annulus, Set.mem_ofPred_eq, hzero, norm_zero] at hx
      linarith [hx.1]
    apply annular_odd_dimension_bound n m hn hm (fun x => f (unitRadial x))
    · exact hf.comp (unitRadial_continuousOn ha) (fun x hx => unitRadial_norm (ha x hx))
    · intro x hx
      exact hfn _ (unitRadial_norm (ha x hx))
    · intro x hx
      rw [unitRadial_neg, hfo _ (unitRadial_norm (ha x hx))]
  · have hm0 : m = 0 := by omega
    subst m
    let x : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single ⟨0,hn⟩ 1
    have hx : ‖x‖ = 1 := by simp [x]
    have hzero : f x = 0 := Subsingleton.elim _ _
    have hh := hfn x hx
    rw [hzero, norm_zero] at hh
    exact False.elim (zero_ne_one hh)

end BorsukNine.SimplicialChains

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Simplicial_OddSphereDimensionBoundFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine.SimplicialChains

lemma odd_sphere_dimension_bound_fintype {α β : Type*} [Fintype α] [Fintype β]
    [Nonempty α] (f : EuclideanSpace ℝ α → EuclideanSpace ℝ β)
    (hf : ContinuousOn f {x | ‖x‖ = 1}) (hfn : ∀ x, ‖x‖ = 1 → ‖f x‖ = 1)
    (hfo : ∀ x, ‖x‖ = 1 → f (-x) = -f x) : Fintype.card α ≤ Fintype.card β := by
  let A := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Fintype.equivFin α)
  let B := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Fintype.equivFin β)
  apply odd_sphere_dimension_bound (Fintype.card α) (Fintype.card β)
    Fintype.card_pos (fun x => B (f (A.symm x)))
  · exact B.continuous.comp_continuousOn (hf.comp A.symm.continuous.continuousOn
      (fun x hx => by simpa using hx))
  · intro x hx
    rw [B.norm_map, hfn _ (by simpa using hx)]
  · intro x hx
    rw [map_neg, hfo _ (by simpa using hx), map_neg]

end BorsukNine.SimplicialChains

namespace BorsukNine
open scoped RealInnerProductSpace

section LabelBound
variable {ν ι : Type*} [Fintype ν] [LinearOrder ν] [Nonempty ν] [Fintype ι]

lemma Admissible.label_bound {f : EuclideanSpace ℝ ν → ι → ℝ} (hf : Admissible f) :
    Fintype.card (UpperTriangle ν) ≤ Fintype.card ι := by
  let : Nonempty (UpperTriangle ν) := by
    obtain ⟨index⟩ := ‹Nonempty ν›
    exact ⟨⟨(index, index), le_rfl⟩⟩
  exact SimplicialChains.odd_sphere_dimension_bound_fintype (sphereExtension f)
    hf.sphereExtension_continuousOn (fun _ hx => hf.sphereExtension_norm hx)
    (fun x _ => sphereExtension_odd f x)

end LabelBound

end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Projectors_Restrict
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace
section Restrict
variable {V W ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [Fintype ι]

lemma Admissible.comp_isometry {f : V → ι → ℝ} (hf : Admissible f) (e : W →ₗᵢ[ℝ] V) :
    Admissible (fun x => f (e x)) := by
  refine ⟨fun i => (hf.smooth i).comp e.contDiff,?_,?_,?_,?_⟩
  · intro x i
    rw [map_neg,hf.antipodal]
  · intro x hx i
    exact hf.nonneg _ ((e.norm_map x).trans hx) i
  · intro x hx
    exact hf.sum_one _ ((e.norm_map x).trans hx)
  · intro x y hx hy hxy i
    exact hf.orthogonal _ _ ((e.norm_map x).trans hx) ((e.norm_map y).trans hy)
      ((e.inner_map_map x y).trans hxy) i

lemma Admissible.restrict_labels {f : V → ι → ℝ} (hf : Admissible f)
    (s : Finset ι) (hzero : ∀ x, ‖x‖ = 1 → ∀ i ∉ s, f x i = 0) :
    Admissible (fun x (i : s) => f x i.val) := by
  classical
  refine ⟨fun i => hf.smooth i.val,fun x i => hf.antipodal x i.val,
    fun x hx i => hf.nonneg x hx i.val,?_,fun x y hx hy hxy i => hf.orthogonal x y hx hy hxy i.val⟩
  intro x hx
  rw [← hf.sum_one x hx]
  rw [Finset.sum_coe_sort]
  exact Finset.sum_subset (Finset.subset_univ s) (fun i _ hi => hzero x hx i hi)

end Restrict

lemma orthogonal_isometry (k : ℕ) {u : EuclideanSpace ℝ (Fin (k+1))} (hu : ‖u‖ = 1) :
    ∃ e : EuclideanSpace ℝ (Fin k) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (k+1)),
      ∀ x, ⟪u,e x⟫ = 0 := by
  let W := (Submodule.span ℝ {u})ᗮ
  have hu0 : u ≠ 0 := by intro h; simp [h] at hu
  have hdim : Module.finrank ℝ W = k := by
    let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (k+1))) = k+1) := ⟨by simp⟩
    exact Submodule.finrank_orthogonal_span_singleton hu0
  let b := (stdOrthonormalBasis ℝ W).reindex (finCongr hdim)
  refine ⟨W.subtypeₗᵢ.comp b.repr.symm.toLinearIsometry,?_⟩
  intro x
  exact (Submodule.mem_orthogonal_singleton_iff_inner_right.mp (b.repr.symm x).property)

end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Support_ActiveChambers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace
section ActiveChambers
variable {E W ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [Fintype ι]

lemma Admissible.commonPositiveCone_isOpen {f : E → ι → ℝ} (hf : Admissible f)
    (I : Finset ι) : IsOpen (commonPositiveCone f I) := by
  have he : commonPositiveCone f I =
      ⋂ i ∈ (I : Set ι), {x | 0 < homogeneousLift f x i} := by ext x; simp [commonPositiveCone]
  rw [he]
  exact isOpen_biInter_finset (fun i _ => isOpen_lt continuous_const
    ((continuous_apply i).comp hf.lift_continuous))

lemma Admissible.commonPositiveCone_safe {f : E → ι → ℝ} (hf : Admissible f)
    (I : Finset ι) : commonPositiveCone f I ⊆ safeNormals (activeVectors f I) := by
  intro x hx z hz horth
  obtain ⟨i,hi,hzi⟩ := hz
  have hxz := mul_pos (hx i hi) hzi
  rw [hf.lift_orthogonal horth i] at hxz
  exact (lt_irrefl 0) hxz

lemma Admissible.commonPositiveCone_interior_safe {f : E → ι → ℝ}
    (hf : Admissible f) (I : Finset ι) :
    commonPositiveCone f I ⊆ interior (safeNormals (activeVectors f I)) :=
  interior_maximal (hf.commonPositiveCone_safe I) (hf.commonPositiveCone_isOpen I)

end ActiveChambers
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
local notation "M" => Matrix ν ν ℝ
local notation "op" => Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)

omit [DecidableEq ν] [Nonempty ν] [DecidableEq ι] in
lemma Admissible.safe_orthogonal_zero {f : E → ι → ℝ} (hf : Admissible f)
    {I : Finset ι} {u v : E} (hu : u ∈ safeNormals (activeVectors f I))
    (hv : ‖v‖ = 1) (horth : ⟪u,v⟫ = 0) {i : ι} (hi : i ∈ I) : f v i = 0 := by
  apply le_antisymm _ (hf.nonneg v hv i)
  apply le_of_not_gt
  intro hp
  exact hu v ⟨i,hi,by rwa [homogeneousLift_unit f hv]⟩ horth

omit [DecidableEq ι] in
lemma Admissible.positiveExtension_safe_zero {f : E → ι → ℝ} (hf : Admissible f)
    {I : Finset ι} {u : E} (hu : u ∈ safeNormals (activeVectors f I))
    {Q : M} (hQ : 0 ≤ Q) (hQu : op Q u = 0) {i : ι} (hi : i ∈ I) :
    positiveExtension f Q i = 0 := by
  apply le_antisymm _ (hf.positiveExtension_nonneg Q i)
  apply le_of_not_gt
  intro hp
  obtain ⟨v,⟨x,hx⟩,hv,hvi⟩ := (hf.positiveExtension_support hQ i).mp hp
  have horth : ⟪u,v⟫ = 0 := by rw [← hx]; exact matrix_image_orthogonal_kernel hQ.isSelfAdjoint hQu x
  exact (ne_of_gt hvi) (hf.safe_orthogonal_zero hu hv horth hi)

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

omit [DecidableEq ν] [Nonempty ν] [Fintype ι] [DecidableEq ι] in
lemma orientedLevel_cone {f : E → ι → ℝ} {I : Finset ι} {w : E} {r : ι → ℝ}
    (hr : ∀ i ∈ I, 0 < r i) {u : E} (hu : u ∈ orientedLevel f w r) :
    u ∈ commonPositiveCone f I := by
  intro i hi
  rw [homogeneousLift_unit f hu.1,hu.2.1]
  exact hr i hi

end PurityGeometry
end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_MatrixGeometry_FibreHomotopy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
open Set
section FibreHomotopy
variable {ν ι : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν] [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ ν
local notation "M" => Matrix ν ν ℝ

lemma Admissible.negativeCoordinates_sum {f : E → ι → ℝ} (hf : Admissible f)
    {I : Finset ι} {u : E} (hu : u ∈ safeNormals (activeVectors f I))
    {Q : M} (hQ : Q ∈ matrixFibre u) :
    (∑ i, negativeCoordinates f I Q i) = 1 := by
  have hz : ∀ i ∈ I, positiveExtension f Q i = 0 := fun i hi =>
    hf.positiveExtension_safe_zero hu hQ.1 hQ.2.2 hi
  have hs := hf.positiveExtension_sum hQ.1
  rw [hQ.2.1] at hs
  have he : ∑ i : ↥(Iᶜ : Finset ι), positiveExtension f Q i.val =
      ∑ i : ι, positiveExtension f Q i := by
    rw [Finset.sum_coe_sort]
    exact Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => hz i (by simpa using hi))
  exact he.trans hs

end FibreHomotopy
end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_MatrixGeometry_FibreContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
open Set
section FibreContinuity
variable {ν ι : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν] [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ ν
local notation "M" => Matrix ν ν ℝ

lemma Admissible.negativeCoordinates_continuousOn {f : E → ι → ℝ} (hf : Admissible f)
    (I : Finset ι) : ContinuousOn (negativeCoordinates f I) {Q : M | 0 ≤ Q} := by
  apply (PiLp.continuous_toLp 2 _).comp_continuousOn
  apply continuousOn_pi.mpr
  intro i
  exact (continuous_apply i.val).comp_continuousOn hf.positiveExtension_continuousOn

end FibreContinuity
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
open scoped RealInnerProductSpace
section DisjointChambers
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
lemma compact_disjoint_chambers {Z K : Set E} (hK : IsCompact K)
    (hsub : K ⊆ interior (safeNormals Z)) :
    ∃ C : Finset E, (↑C : Set E) ⊆ K ∧
      (Pairwise (fun c d : ↥C => Disjoint (interior (signChamber Z c.val))
        (interior (signChamber Z d.val)))) ∧
      K ⊆ ⋃ c : ↥C, interior (signChamber Z c.val) := by
  classical
  obtain ⟨C,hCK,hcover⟩ := compact_finite_chambers hK hsub
  let g : E → Set E := fun c => interior (signChamber Z c)
  have hsurj : (↑C : Set E).SurjOn g (↑(C.image g) : Set (Set E)) := by
    intro U hU
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hU
    exact ⟨c,hc,rfl⟩
  obtain ⟨D,hDC,hDinj,hDimage⟩ := Finset.exists_subset_injOn_image_eq_of_surjOn
    (↑C : Set E) (C.image g) hsurj
  refine ⟨D,fun c hc => hCK (hDC hc),?_,?_⟩
  · intro c d hne
    rcases signChamber_eq_or_disjoint Z c.val d.val with he | hdj
    · exfalso
      exact hne (Subtype.ext (hDinj c.property d.property (congrArg interior he)))
    · exact hdj.mono interior_subset interior_subset
  · intro x hx
    obtain ⟨c,hc,hxc⟩ := Set.mem_iUnion₂.mp (hcover hx)
    have hg : g c ∈ D.image g := by rw [hDimage]; exact Finset.mem_image.mpr ⟨c,hc,rfl⟩
    obtain ⟨d,hd,hgd⟩ := Finset.mem_image.mp hg
    exact Set.mem_iUnion.mpr ⟨⟨d,hd⟩,by change x ∈ g d; rw [hgd]; exact hxc⟩
end DisjointChambers
end BorsukNine

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

omit [DecidableEq ν] in
lemma matrixEmbed_nonneg (e : D →ₗᵢ[ℝ] E) {B : Matrix μ μ ℝ} (hB : 0 ≤ B) :
    0 ≤ matrixEmbed e B := ((Matrix.nonneg_iff_posSemidef.mp hB).mul_mul_conjTranspose_same _).nonneg

lemma matrixEmbed_trace (e : D →ₗᵢ[ℝ] E) (B : Matrix μ μ ℝ) :
    Matrix.trace (matrixEmbed e B) = Matrix.trace B := by
  change Matrix.trace (isometryMatrix e * B * (isometryMatrix e)ᴴ) = Matrix.trace B
  rw [Matrix.trace_mul_comm,← Matrix.mul_assoc,isometryMatrix_star_mul,Matrix.one_mul]

lemma matrixEmbed_kernel (e : D →ₗᵢ[ℝ] E) (B : Matrix μ μ ℝ) {u : E}
    (hu : ∀ x : D, ⟪u,e x⟫ = 0) :
    Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ) (matrixEmbed e B) u = 0 := by
  have hz : Matrix.toEuclideanLin (isometryMatrix e)ᴴ u = 0 := by
    apply ext_inner_left ℝ
    intro x
    rw [inner_zero_right,Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    change ⟪x,(Matrix.toEuclideanLin (isometryMatrix e)).adjoint u⟫ = 0
    rw [LinearMap.adjoint_inner_right,isometryMatrix_action,real_inner_comm]
    exact hu x
  change Matrix.toEuclideanLin (isometryMatrix e * B * (isometryMatrix e)ᴴ) u = 0
  rw [toEuclideanLin_mul]
  change Matrix.toEuclideanLin (isometryMatrix e * B) (Matrix.toEuclideanLin (isometryMatrix e)ᴴ u) = 0
  rw [hz,map_zero]

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

lemma matrixCompress_trace (e : D →ₗᵢ[ℝ] E) {Q : Matrix ν ν ℝ}
    (hQ : IsSelfAdjoint Q)
    (hR : LinearMap.range (Matrix.toEuclideanLin Q) ≤ LinearMap.range e.toLinearMap) :
    Matrix.trace (matrixCompress e Q) = Matrix.trace Q := by
  rw [← matrixEmbed_trace e,matrixEmbed_compress e hQ hR]

end MatrixCompression

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
open scoped Matrix RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
section SymmetricEntries
variable {ν : Type*} [Fintype ν] [LinearOrder ν]

omit [Fintype ν] in
lemma symmetricCoordinates_entries {Q : Matrix ν ν ℝ} (hQ : IsSelfAdjoint Q) :
    symmetricCoordinates (symmetricEntries Q) = Q := by
  ext i j
  change (if h : i ≤ j then Q i j else Q j i) = Q i j
  split_ifs with h
  · rfl
  · have he := congrArg (fun B : Matrix ν ν ℝ => B i j) hQ.star_eq
    simpa only [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply,star_trivial] using he

end SymmetricEntries
end BorsukNine

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

lemma simplexProjection_sum {ι : Type*} [Fintype ι] [Nonempty ι] (x : EuclideanSpace ℝ ι) :
    coordinateSum (simplexProjection x) = 1 := by
  simp only [simplexProjection,zeroSumProjection,sub_apply,ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply,map_add,map_sub,map_smul,coordinateSum_uniform,
    smul_eq_mul,mul_one,sub_self,zero_add]

lemma simplexProjection_fixed {ι : Type*} [Fintype ι] {x : EuclideanSpace ℝ ι}
    (hx : coordinateSum x = 1) : simplexProjection x = x := by
  simp only [simplexProjection,zeroSumProjection,sub_apply,ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply,hx,one_smul,sub_add_cancel]

lemma simplexProjection_sub_fixed {ι : Type*} [Fintype ι] {x y : EuclideanSpace ℝ ι}
    (hy : coordinateSum y = 1) : simplexProjection x - y = zeroSumProjection ι (x-y) := by
  rw [map_sub]
  have hy' := simplexProjection_fixed hy
  change zeroSumProjection ι y + uniformVector ι = y at hy'
  change (zeroSumProjection ι x + uniformVector ι) - y = _
  calc
    _ = (zeroSumProjection ι x + uniformVector ι) -
      (zeroSumProjection ι y + uniformVector ι) := by rw [hy']
    _ = _ := by abel

lemma continuous_simplex_approx {D ι : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [FiniteDimensional ℝ D] [Fintype ι] [Nonempty ι]
    (g : D → EuclideanSpace ℝ ι) (hg : Continuous g)
    {K : Set D} (hK : ∀ x ∈ K, coordinateSum (g x) = 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ a : D → EuclideanSpace ℝ ι, ContDiff ℝ (⊤ : ℕ∞) a ∧
      (∀ x, coordinateSum (a x) = 1) ∧ (∀ x ∈ K, ‖a x - g x‖ < ε) := by
  have hp := norm_nonneg (zeroSumProjection ι)
  have hδ : 0 < ε / (‖zeroSumProjection ι‖ + 1) := div_pos hε (by positivity)
  obtain ⟨b,hb,hbg,-⟩ := hg.exists_contDiff_approx (⊤ : ℕ∞)
    (continuous_const : Continuous (fun _ : D => ε / (‖zeroSumProjection ι‖ + 1))) (fun _ => hδ)
  let a := fun x => simplexProjection (b x)
  refine ⟨a,?_,fun x => simplexProjection_sum (b x),?_⟩
  · exact ((zeroSumProjection ι).contDiff.comp hb).add contDiff_const
  · intro x hx
    change ‖simplexProjection (b x) - g x‖ < ε
    rw [simplexProjection_sub_fixed (hK x hx)]
    have hd : ‖b x - g x‖ < ε / (‖zeroSumProjection ι‖ + 1) := by
      simpa only [dist_eq_norm] using hbg x
    calc
      _ ≤ ‖zeroSumProjection ι‖ * ‖b x - g x‖ := (zeroSumProjection ι).le_opNorm _
      _ ≤ ‖zeroSumProjection ι‖ * (ε / (‖zeroSumProjection ι‖ + 1)) := mul_le_mul_of_nonneg_left hd.le hp
      _ < ε := by
        have he : (‖zeroSumProjection ι‖+1) * (ε / (‖zeroSumProjection ι‖+1)) = ε :=
          mul_div_cancel₀ ε (by positivity)
        nlinarith

end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Projectors_NullImage
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open Set MeasureTheory
open scoped Topology

section NullImage
variable {D T : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup T] [NormedSpace ℝ T] [FiniteDimensional ℝ T]
  [MeasurableSpace T] [BorelSpace T]

lemma differentiable_image_null_of_projection (μ : Measure T) [μ.IsAddHaarMeasure]
    (p : T →L[ℝ] D) (hp : Function.Surjective p) (hpn : ¬ Function.Injective p)
    {f : D → T} {S : Set D} (hf : ∀ x ∈ S, DifferentiableAt ℝ f x) : μ (f '' S) = 0 := by
  let g : T → T := fun x => f (p x)
  let g' : T → T →L[ℝ] T := fun x => (fderiv ℝ f (p x)).comp p
  have hd : ∀ x ∈ p ⁻¹' S, HasFDerivWithinAt g (g' x) (p ⁻¹' S) x := by
    intro x hx
    exact ((hf (p x) hx).hasFDerivAt.comp x p.hasFDerivAt).hasFDerivWithinAt
  have hdet : ∀ x ∈ p ⁻¹' S, (g' x).det = 0 := by
    intro x _
    change ((g' x).toLinearMap).det = 0
    apply LinearMap.det_eq_zero_iff_ker_ne_bot.mpr
    apply mt LinearMap.ker_eq_bot.mp
    intro hinj
    exact hpn (fun u v huv => hinj (by change fderiv ℝ f (p x) (p u) = fderiv ℝ f (p x) (p v); rw [huv]))
  have he : g '' (p ⁻¹' S) = f '' S := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact ⟨p x,hx,rfl⟩
    · rintro ⟨x,hx,rfl⟩
      obtain ⟨z,rfl⟩ := hp x
      exact ⟨z,hx,rfl⟩
  rw [← he]
  exact addHaar_image_eq_zero_of_det_fderivWithin_eq_zero μ hd hdet

end NullImage

lemma initialProjection_surjective (n m : ℕ) (h : n ≤ m) :
    Function.Surjective (initialProjection n m h) := by
  intro x
  refine ⟨WithLp.toLp 2 (fun j : Fin m => if h : j.val < n then x ⟨j.val,h⟩ else 0),?_⟩
  apply PiLp.ext
  intro i
  change (if hj : i.val < n then x ⟨i.val,hj⟩ else 0) = x i
  simp only [dite_eq_left i.isLt]

lemma initialProjection_not_injective (n m : ℕ) (h : n < m) :
    ¬ Function.Injective (initialProjection n m h.le) := by
  intro hh
  have hl := LinearMap.finrank_le_finrank_of_injective
    (f := (initialProjection n m h.le).toLinearMap) hh
  simp only [finrank_euclideanSpace_fin] at hl
  omega

lemma differentiable_image_null_of_dim_lt (n m : ℕ) (h : n < m)
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {S : Set (EuclideanSpace ℝ (Fin n))} (hf : ∀ x ∈ S, DifferentiableAt ℝ f x) :
    volume (f '' S) = 0 :=
  differentiable_image_null_of_projection volume (initialProjection n m h.le)
    (initialProjection_surjective n m h.le) (initialProjection_not_injective n m h) hf

end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Projectors_FiniteSmoothSliceMisses
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped BigOperators
open MeasureTheory Set

lemma finite_smooth_slice_misses (n m : ℕ) (hnm : n < m)
    {κ : Type*} [Fintype κ] (L : κ → EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (g : κ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (hg : ∀ c, ContDiff ℝ (⊤ : ℕ∞) (g c))
    {V : Set (EuclideanSpace ℝ (Fin m))} (hVo : IsOpen V) (hVn : V.Nonempty)
    (hVp : ∀ y ∈ V, ∀ i, 0 < y i) :
    ∃ z : EuclideanSpace ℝ (Fin m), (∃ y ∈ V, z = (∑ i, y i)⁻¹ • y) ∧
      (∀ i, 0 < z i) ∧ (∑ i, z i) = 1 ∧
      ∀ c x, L c x = 1 → g c x ≠ z := by
  classical
  let C (c : κ) (x : EuclideanSpace ℝ (Fin n)) := L c x • g c ((L c x)⁻¹ • x)
  have hCd (c : κ) : ∀ x ∈ {x | L c x ≠ 0}, DifferentiableAt ℝ (C c) x := by
    intro x hx
    exact (L c).differentiableAt.smul
      (((hg c).differentiable (by simp)).differentiableAt.comp x
        (((L c).differentiableAt.inv hx).smul differentiableAt_id))
  have hnull : volume (⋃ c : κ, C c '' {x | L c x ≠ 0}) = 0 := by
    exact measure_iUnion_null (fun c => differentiable_image_null_of_dim_lt n m hnm (hCd c))
  obtain ⟨y,hy,hym⟩ : ∃ y ∈ V, y ∉ ⋃ c : κ, C c '' {x | L c x ≠ 0} := by
    by_contra hn
    push Not at hn
    have hl : volume V ≤ volume (⋃ c : κ, C c '' {x | L c x ≠ 0}) := measure_mono hn
    rw [hnull] at hl
    exact hVo.measure_ne_zero volume hVn (le_antisymm hl (zero_le))
  let s : ℝ := ∑ i, y i
  have hs : 0 < s := Finset.sum_pos (fun i _ => hVp y hy i)
    (Finset.univ_nonempty_iff.mpr ⟨⟨0,by omega⟩⟩)
  let z : EuclideanSpace ℝ (Fin m) := s⁻¹ • y
  refine ⟨z,⟨y,hy,rfl⟩,fun i => ?_,?_,?_⟩
  · change 0 < s⁻¹ * y i
    exact mul_pos (inv_pos.mpr hs) (hVp y hy i)
  · change (∑ i, s⁻¹ * y i) = 1
    rw [← Finset.mul_sum]
    exact inv_mul_cancel₀ (ne_of_gt hs)
  · intro c x hx he
    apply hym
    apply Set.mem_iUnion.mpr
    refine ⟨c,s • x,?_,?_⟩
    · simp only [Set.mem_ofPred_eq,map_smul,hx,smul_eq_mul,mul_one]
      exact ne_of_gt hs
    · simp only [C,map_smul,hx,smul_eq_mul,mul_one,inv_smul_smul₀ (ne_of_gt hs),he,z,
        smul_inv_smul₀ (ne_of_gt hs)]

end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Projectors_FiniteSmoothSliceMissesBounded
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped BigOperators
lemma finite_smooth_slice_misses_bounded (n m : ℕ) (hnm : n < m)
    {κ : Type*} [Fintype κ] (L : κ → EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (g : κ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (hg : ∀ c, ContDiff ℝ (⊤ : ℕ∞) (g c)) :
    ∃ z : EuclideanSpace ℝ (Fin m), (∀ i, (2*(m:ℝ))⁻¹ < z i) ∧
      (∑ i, z i) = 1 ∧ ∀ c x, L c x = 1 → g c x ≠ z := by
  have hm : 0 < m := by omega
  let V : Set (EuclideanSpace ℝ (Fin m)) := {y | ∀ i, 1 < y i ∧ y i < 2}
  have hVo : IsOpen V := by
    have he : V = ⋂ i, {y : EuclideanSpace ℝ (Fin m) | 1 < y i ∧ y i < 2} := by
      ext y; simp [V]
    rw [he]
    exact isOpen_iInter_of_finite (fun i => (isOpen_lt continuous_const
      (PiLp.continuous_apply 2 (fun _ : Fin m => ℝ) i)).inter
      (isOpen_lt (PiLp.continuous_apply 2 (fun _ : Fin m => ℝ) i) continuous_const))
  have hVn : V.Nonempty := ⟨WithLp.toLp 2 (fun _ => (3/2:ℝ)),fun _ => by norm_num⟩
  obtain ⟨z,⟨y,hy,hz⟩,hp,hs,hmiss⟩ := finite_smooth_slice_misses n m hnm L g hg
    hVo hVn (fun y hy i => lt_trans zero_lt_one (hy i).1)
  have hmm : (0:ℝ) < m := Nat.cast_pos.mpr hm
  have hsum : 0 < ∑ i, y i := Finset.sum_pos (fun i _ => by linarith [(hy i).1])
    (Finset.univ_nonempty_iff.mpr ⟨⟨0,hm⟩⟩)
  have hbound : ∑ i, y i < 2*(m:ℝ) := by
    have hh := Finset.sum_lt_sum_of_nonempty (s := Finset.univ)
      (Finset.univ_nonempty_iff.mpr ⟨⟨0,hm⟩⟩) (fun i _ => (hy i).2)
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_comm] using hh
  refine ⟨z,?_,hs,hmiss⟩
  intro i
  rw [hz]
  change (2*(m:ℝ))⁻¹ < (∑ i, y i)⁻¹ * y i
  have hinv : (2*(m:ℝ))⁻¹ < (∑ i, y i)⁻¹ := by
    exact (inv_lt_inv₀ (by positivity) hsum).mpr hbound
  exact hinv.trans (by nlinarith [(hy i).1,inv_pos.mpr hsum])

lemma finite_smooth_slice_misses_general {D ι κ : Type*}
    [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D]
    [Fintype ι] [Fintype κ]
    (hd : Module.finrank ℝ D < Fintype.card ι)
    (L : κ → D →L[ℝ] ℝ) (g : κ → D → EuclideanSpace ℝ ι)
    (hg : ∀ c, ContDiff ℝ (⊤ : ℕ∞) (g c)) :
    ∃ z : EuclideanSpace ℝ ι, (∀ i, (2*(Fintype.card ι:ℝ))⁻¹ < z i) ∧
      (∑ i, z i) = 1 ∧ ∀ c x, L c x = 1 → g c x ≠ z := by
  let eD := (stdOrthonormalBasis ℝ D).repr
  let eY := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Fintype.equivFin ι)
  let L' := fun c => (L c).comp eD.symm.toContinuousLinearEquiv.toContinuousLinearMap
  let g' := fun c x => eY (g c (eD.symm x))
  have hg' (c : κ) : ContDiff ℝ (⊤ : ℕ∞) (g' c) :=
    eY.toContinuousLinearEquiv.contDiff.comp ((hg c).comp eD.symm.toContinuousLinearEquiv.contDiff)
  obtain ⟨z,hp,hs,hm⟩ := finite_smooth_slice_misses_bounded _ _ hd L' g' hg'
  have heY (q : EuclideanSpace ℝ (Fin (Fintype.card ι))) (i : ι) :
      (eY.symm q) i = q ((Fintype.equivFin ι) i) := by
    simp [eY, LinearIsometryEquiv.piLpCongrLeft_symm,
      LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft']
  refine ⟨eY.symm z,?_,?_,?_⟩
  · intro i
    rw [heY]
    exact hp ((Fintype.equivFin ι) i)
  · simp only [heY]
    rw [Equiv.sum_comp]
    exact hs
  · intro c x hx he
    apply hm c (eD x)
    · simpa only [L',ContinuousLinearMap.comp_apply,LinearIsometryEquiv.coe_toContinuousLinearEquiv,
        ContinuousLinearEquiv.coe_coe,LinearIsometryEquiv.symm_apply_apply] using hx
    · change eY (g c (eD.symm (eD x))) = z
      rw [LinearIsometryEquiv.symm_apply_apply,he,LinearIsometryEquiv.apply_symm_apply]
end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_MatrixGeometry_CenterApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
open Set
section CenterApproximation
variable {k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "D" => EuclideanSpace ℝ (UpperTriangle (Fin k))
local notation "W" => EuclideanSpace ℝ (Fin k)
local notation "E" => EuclideanSpace ℝ (Fin (k+1))
local notation "M" => Matrix (Fin (k+1)) (Fin (k+1)) ℝ
local notation "op" => Matrix.toEuclideanCLM (n := Fin (k+1)) (𝕜 := ℝ)

lemma matrixFibre_range {u : E} (e : W →ₗᵢ[ℝ] E)
    (he : ∀ v, ⟪u,v⟫ = 0 → ∃ x, e x = v) {Q : M} (hQ : Q ∈ matrixFibre u) :
    LinearMap.range (Matrix.toEuclideanLin Q) ≤ LinearMap.range e.toLinearMap := by
  rintro v ⟨b,rfl⟩
  obtain ⟨x,hx⟩ := he (op Q b) (matrix_image_orthogonal_kernel hQ.1.isSelfAdjoint hQ.2.2 b)
  exact ⟨x,hx⟩

lemma matrixCompress_mem_slice {u : E} (e : W →ₗᵢ[ℝ] E)
    (he : ∀ v, ⟪u,v⟫ = 0 → ∃ x, e x = v) {Q : M} (hQ : Q ∈ matrixFibre u) :
    0 ≤ matrixCompress e Q ∧ Matrix.trace (matrixCompress e Q) = 1 :=
  ⟨matrixCompress_nonneg e hQ.1,
    (matrixCompress_trace e hQ.1.isSelfAdjoint (matrixFibre_range e he hQ)).trans hQ.2.1⟩

lemma Admissible.center_approximation {f : E → ι → ℝ} (hf : Admissible f)
    {I : Finset ι} [Nonempty ↥(Iᶜ : Finset ι)] {c : E}
    (hc : c ∈ safeNormals (activeVectors f I)) (e : W →ₗᵢ[ℝ] E)
    (he : ∀ x, ⟪c,e x⟫ = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : D → EuclideanSpace ℝ ↥(Iᶜ : Finset ι), ContDiff ℝ (⊤ : ℕ∞) a ∧
      (∀ x, ∑ i, a x i = 1) ∧
      ∀ x, 0 ≤ symmetricCoordinates x → Matrix.trace (symmetricCoordinates x) = 1 →
        ‖a x - negativeCoordinates f I (matrixEmbed e (symmetricCoordinates x))‖ < ε := by
  let g : D → EuclideanSpace ℝ ↥(Iᶜ : Finset ι) :=
    fun x => negativeCoordinates f I (matrixEmbed e ((symmetricCoordinates x)⁺))
  have hP : Continuous (fun x : D => (symmetricCoordinates x)⁺) :=
    matrix_posPart_continuousOn.comp_continuous symmetricCoordinates.continuous_of_finiteDimensional
      (fun x => symmetricCoordinates_selfAdjoint x)
  have hg : Continuous g :=
    (hf.negativeCoordinates_continuousOn I).comp_continuous
      ((matrixEmbed e).continuous_of_finiteDimensional.comp hP)
      (fun x => matrixEmbed_nonneg e (CFC.posPart_nonneg _))
  let K : Set D := {x | 0 ≤ symmetricCoordinates x ∧ Matrix.trace (symmetricCoordinates x) = 1}
  have hs : ∀ x ∈ K, coordinateSum (g x) = 1 := by
    intro x hx
    change ∑ i, negativeCoordinates f I (matrixEmbed e ((symmetricCoordinates x)⁺)) i = 1
    rw [(CFC.posPart_eq_self _).mpr hx.1]
    apply hf.negativeCoordinates_sum hc
    exact ⟨matrixEmbed_nonneg _ hx.1,(matrixEmbed_trace _ _).trans hx.2,matrixEmbed_kernel e _ he⟩
  obtain ⟨a,ha,has,hae⟩ := continuous_simplex_approx g hg hs hε
  refine ⟨a,ha,has,?_⟩
  intro x hx ht
  have hh := hae x ⟨hx,ht⟩
  simpa only [g,(CFC.posPart_eq_self _).mpr hx] using hh

lemma Admissible.finite_center_approximations {κ : Type*} [Fintype κ]
    {f : E → ι → ℝ} (hf : Admissible f) {I : Finset ι}
    (hd : Fintype.card (UpperTriangle (Fin k)) < Fintype.card ↥(Iᶜ : Finset ι))
    (c : κ → E) (hc : ∀ j, c j ∈ safeNormals (activeVectors f I)) (hcn : ∀ j, ‖c j‖ = 1) :
    ∃ z : EuclideanSpace ℝ ↥(Iᶜ : Finset ι), (∀ i, (2*(Fintype.card ↥(Iᶜ : Finset ι):ℝ))⁻¹ < z i) ∧
      (∑ i, z i) = 1 ∧
      ∃ g : κ → M → EuclideanSpace ℝ ↥(Iᶜ : Finset ι), (∀ j, Continuous (g j)) ∧
        (∀ j, ∀ Q ∈ matrixFibre (c j), (∑ i, g j Q i) = 1) ∧
        (∀ j, ∀ Q ∈ matrixFibre (c j), ‖g j Q - negativeCoordinates f I Q‖ <
          (2*(Fintype.card ↥(Iᶜ : Finset ι):ℝ))⁻¹) ∧
        (∀ j, ∀ Q ∈ matrixFibre (c j), g j Q ≠ z) := by
  have hj : 0 < Fintype.card ↥(Iᶜ : Finset ι) := lt_of_le_of_lt (Nat.zero_le _) hd
  let : Nonempty ↥(Iᶜ : Finset ι) := Fintype.card_pos_iff.mp hj
  let ε : ℝ := (2*(Fintype.card ↥(Iᶜ : Finset ι):ℝ))⁻¹
  have hε : 0 < ε := by dsimp [ε]; positivity
  choose e he hes using (fun j => orthogonal_frame k (hcn j))
  choose a ha has hae using (fun j => hf.center_approximation (hc j) (e j) (he j) hε)
  let L : D →L[ℝ] ℝ := (Matrix.traceLinearMap (Fin k) ℝ ℝ).toContinuousLinearMap.comp
    (symmetricCoordinates (ν := Fin k)).toContinuousLinearMap
  have hendim : Module.finrank ℝ D < Fintype.card ↥(Iᶜ : Finset ι) := by simpa using hd
  obtain ⟨z,hzp,hzs,hzm⟩ := finite_smooth_slice_misses_general hendim (fun _ : κ => L) a ha
  let g : κ → M → EuclideanSpace ℝ ↥(Iᶜ : Finset ι) :=
    fun j Q => a j (symmetricEntries (matrixCompress (e j) Q))
  refine ⟨z,hzp,hzs,g,?_,?_,?_,?_⟩
  · intro j
    exact (ha j).continuous.comp (symmetricEntries.continuous_of_finiteDimensional.comp
      (matrixCompress (e j)).continuous_of_finiteDimensional)
  · intro j Q hQ
    exact has j _
  · intro j Q hQ
    have hCQ := matrixCompress_mem_slice (e j) (hes j) hQ
    have hSC := symmetricCoordinates_entries hCQ.1.isSelfAdjoint
    have hEQ := matrixEmbed_compress (e j) hQ.1.isSelfAdjoint (matrixFibre_range (e j) (hes j) hQ)
    have hh := hae j (symmetricEntries (matrixCompress (e j) Q))
      (by rw [hSC]; exact hCQ.1) (by rw [hSC]; exact hCQ.2)
    simpa only [hSC,hEQ,g,ε] using hh
  · intro j Q hQ
    apply hzm j _
    change Matrix.trace (symmetricCoordinates (symmetricEntries (matrixCompress (e j) Q))) = 1
    have hCQ := matrixCompress_mem_slice (e j) (hes j) hQ
    rw [symmetricCoordinates_entries hCQ.1.isSelfAdjoint]
    exact hCQ.2

end CenterApproximation
end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Support_Purity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace
open Set
section Purity
variable {k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ (Fin (k+1))

lemma Admissible.maximal_support_complement_bound {f : E → ι → ℝ} (hf : Admissible f)
    (hdim : Fintype.card (UpperTriangle (Fin (k+1))) = Fintype.card ι)
    (hn : 1 < Fintype.card ι) {w : E} (hw : ‖w‖ = 1)
    (hmax : ∀ u : E, ‖u‖ = 1 → positiveSupport f w ⊆ positiveSupport f u →
      positiveSupport f u = positiveSupport f w) :
    Fintype.card ↥((positiveSupport f w)ᶜ : Finset ι) ≤ Fintype.card (UpperTriangle (Fin k)) := by
  classical
  by_contra hb
  have hd : Fintype.card (UpperTriangle (Fin k)) <
      Fintype.card ↥((positiveSupport f w)ᶜ : Finset ι) := lt_of_not_ge hb
  let I := positiveSupport f w
  have hI : I.Nonempty := hf.support_nonempty hw
  have hr : ∀ i ∈ I, 0 < f w i := fun i hi => (mem_positiveSupport f w i).mp hi
  have hro : ∀ i ∉ I, f w i = 0 := by
    intro i hi
    exact le_antisymm (not_lt.mp (fun hp => hi ((mem_positiveSupport f w i).mpr hp))) (hf.nonneg w hw i)
  obtain ⟨C,hCK,hCD,hcover⟩ := compact_disjoint_chambers (hf.orientedLevel_compact w (f w))
    (fun u hu => hf.commonPositiveCone_interior_safe I (orientedLevel_cone hr hu))
  let c : ↥C → E := Subtype.val
  have hc : ∀ j, c j ∈ commonPositiveCone f I := fun j => orientedLevel_cone hr (hCK j.property)
  have hcn : ∀ j, ‖c j‖ = 1 := fun j => (hCK j.property).1
  obtain ⟨z,hz,hzs,g,hg,hgs,hge,hgm⟩ := hf.finite_center_approximations hd c
    (fun j => hf.commonPositiveCone_safe I (hc j)) hcn
  have hj : 0 < Fintype.card ↥(Iᶜ : Finset ι) := lt_of_le_of_lt (Nat.zero_le _) hd
  let : Nonempty ↥(Iᶜ : Finset ι) := Fintype.card_pos_iff.mp hj
  have hε : 0 < (2*(Fintype.card ↥(Iᶜ : Finset ι):ℝ))⁻¹ := by positivity
  exact hf.chart_surgery_impossible hdim hn hI hmax hw hr hr hro (hf.sum_one w hw)
    c hc hcn hCD hcover hε g hg hgs hge z hz hzs hgm

end Purity
end BorsukNine

namespace BorsukNine
open scoped RealInnerProductSpace
section PureFacets
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fintype ι] [DecidableEq ι]
omit [InnerProductSpace ℝ E] [DecidableEq ι] in
lemma exists_maximal_support (f : E → ι → ℝ) {w : E} (hw : ‖w‖ = 1) :
    ∃ u, ‖u‖ = 1 ∧ positiveSupport f w ⊆ positiveSupport f u ∧
      ∀ v, ‖v‖ = 1 → positiveSupport f u ⊆ positiveSupport f v →
        positiveSupport f v = positiveSupport f u := by
  classical
  let S : Set (Finset ι) := {s | ∃ u, ‖u‖ = 1 ∧ positiveSupport f w ⊆ s ∧ positiveSupport f u = s}
  obtain ⟨s,hs,hm⟩ := (Set.toFinite S).exists_maximal (show S.Nonempty from ⟨_,w,hw,Finset.Subset.rfl,rfl⟩)
  obtain ⟨u,hu,hwu,rfl⟩ := hs
  refine ⟨u,hu,hwu,?_⟩
  intro v hv huv
  exact le_antisymm (hm ⟨v,hv,hwu.trans huv,rfl⟩ huv) huv
end PureFacets

end BorsukNine

open Set MeasureTheory

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Support_SupportIncidence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine
open scoped RealInnerProductSpace

section SixPure
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ (Fin 3)
lemma Admissible.support_card_three_le_of_card {f : E → ι → ℝ}
    (hf : Admissible f) (hcard : Fintype.card ι = 6) {u : E} (hu : ‖u‖ = 1) :
    (positiveSupport f u).card ≤ 3 := by
  classical
  obtain ⟨e,he⟩ := orthogonal_isometry 2 hu
  let s := (positiveSupport f u)ᶜ
  have hzero : ∀ x, ‖x‖ = 1 → ∀ i ∉ s, f (e x) i = 0 := by
    intro x hx i hi
    have hip : 0 < f u i := (mem_positiveSupport _ _ _).mp (by simpa [s] using hi)
    have hn := hf.nonneg (e x) (by simpa using hx) i
    exact le_antisymm (le_of_not_gt (fun hp => hf.orthogonal u (e x) hu
      (by simpa using hx) (he x) i ⟨hip,hp⟩)) hn
  have hb := ((hf.comp_isometry e).restrict_labels s hzero).label_bound
  have hc : Fintype.card (UpperTriangle (Fin 2)) = 3 := by decide
  rw [hc,Fintype.card_coe,Finset.card_compl,hcard] at hb
  omega

lemma Admissible.support_extends_three_of_card {f : E → ι → ℝ} (hf : Admissible f)
    (hcard : Fintype.card ι = 6) {w : E} (hw : ‖w‖ = 1) :
    ∃ u, ‖u‖ = 1 ∧ positiveSupport f w ⊆ positiveSupport f u ∧ (positiveSupport f u).card = 3 := by
  obtain ⟨u,hu,hwu,hm⟩ := exists_maximal_support f hw
  have hl := hf.support_card_three_le_of_card hcard hu
  have hdim : Fintype.card (UpperTriangle (Fin 3)) = Fintype.card ι := by rw [hcard]; decide
  have hb := hf.maximal_support_complement_bound (k := 2) hdim (by omega) hu hm
  have hc : Fintype.card (UpperTriangle (Fin 2)) = 3 := by decide
  rw [Fintype.card_coe,Finset.card_compl,hcard,hc] at hb
  exact ⟨u,hu,hwu,by omega⟩

lemma Admissible.face_extends_three_oai {f : E → ι → ℝ} (hf : Admissible f)
    (hcard : Fintype.card ι = 6) {U : Finset ι} (hU : SupportFace f U) :
    ∃ I : Finset ι, I.card = 3 ∧ SupportFace f I ∧ U ⊆ I := by
  obtain ⟨w,hw,hUw⟩ := hU
  obtain ⟨u,hu,hwu,huc⟩ := hf.support_extends_three_of_card hcard hw
  exact ⟨positiveSupport f u,huc,⟨u,hu,Finset.Subset.refl _⟩,hUw.trans hwu⟩

end SixPure

end BorsukNine

end OAI
end

theorem solution.{u_1} : type_of% @OAI.BorsukNine.Admissible.face_extends_three_oai.{u_1} := @OAI.BorsukNine.Admissible.face_extends_three_oai.{u_1}
