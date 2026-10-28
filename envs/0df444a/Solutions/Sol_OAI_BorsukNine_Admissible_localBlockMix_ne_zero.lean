-- Prove2me | solution 1 for OAI.BorsukNine.Admissible.localBlockMix_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T20:57:34.986462+00:00
-- url     : https://prove2.me/submissions/de17200d-13e3-4467-ae86-94afc60377db

import Mathlib
import Definitions.Def_OAIQ058B000

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

lemma matrix_sqrt_smul {Q : Matrix ν ν ℝ} (hQ : 0 ≤ Q) {t : ℝ} (ht : 0 ≤ t) :
    CFC.sqrt (t • Q) = Real.sqrt t • CFC.sqrt Q := by
  apply (CFC.sqrt_eq_iff _ _ (smul_nonneg ht hQ)
    (smul_nonneg (Real.sqrt_nonneg _) (CFC.sqrt_nonneg _))).mpr
  rw [smul_mul_smul, CFC.sqrt_mul_sqrt_self Q hQ, Real.mul_self_sqrt ht]

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

lemma Admissible.lift_even {f : V → ι → ℝ} (hf : Admissible f) (v : V) :
    homogeneousLift f (-v) = homogeneousLift f v := by
  ext i
  simp [homogeneousLift, smul_neg, hf.antipodal]

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

omit [Fintype ι] in
lemma homogeneousLift_smul_nonneg (f : V → ι → ℝ) (v : V) {t : ℝ} (ht : 0 ≤ t) :
    homogeneousLift f (t • v) = t ^ 2 • homogeneousLift f v := by
  rcases ht.eq_or_lt with rfl | hp
  · simp
  · exact homogeneousLift_smul_pos f v hp

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

omit [Nonempty ν] [Fintype ι] in
lemma integralLift_smul_nonneg (f : E → ι → ℝ) (T : E →L[ℝ] E)
    {t : ℝ} (ht : 0 ≤ t) : integralLift f (t • T) = t ^ 2 • integralLift f T := by
  ext i
  simp only [integralLift, smul_apply, homogeneousLift_smul_nonneg f _ ht,
    Pi.smul_apply, smul_eq_mul, integral_const_mul]
  ring

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

lemma matrix_abs_action_norm_sq (A : Matrix ν ν ℝ) (x : Ek) :
    ‖op (CFC.abs A) x‖ ^ 2 = ‖op A x‖ ^ 2 := by
  rw [matrix_action_norm_sq, (CFC.abs_nonneg A).star_eq, CFC.abs_mul_abs,
    ← matrix_action_norm_sq]

lemma matrix_abs_kernel {A : Matrix ν ν ℝ} {x : Ek} (hx : op A x = 0) :
    op (CFC.abs A) x = 0 := by
  apply norm_eq_zero.mp
  apply sq_eq_zero_iff.mp
  rw [matrix_abs_action_norm_sq, hx, norm_zero, zero_pow (by decide : 2 ≠ 0)]

lemma matrix_parts_kernel {A : Matrix ν ν ℝ} (hA : IsSelfAdjoint A)
    {x : Ek} (hx : op A x = 0) : op A⁺ x = 0 ∧ op A⁻ x = 0 := by
  have habs := matrix_abs_kernel hx
  constructor
  · have h := congrArg (fun B : Matrix ν ν ℝ => op B x) (CFC.abs_add_self A hA)
    have hh : (2 : ℝ) • op A⁺ x = 0 := by
      simpa only [map_add, add_apply, two_smul, hx, habs, add_zero] using h.symm
    exact (smul_eq_zero.mp hh).resolve_left (by norm_num)
  · have h := congrArg (fun B : Matrix ν ν ℝ => op B x) (CFC.abs_sub_self A hA)
    have hh : (2 : ℝ) • op A⁻ x = 0 := by
      simpa only [map_sub, sub_apply, two_smul, hx, habs, sub_zero,
        map_add, add_apply] using h.symm
    exact (smul_eq_zero.mp hh).resolve_left (by norm_num)

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

omit [Nonempty ν] [Fintype ι] in
lemma positiveExtension_smul_nonneg (f : E → ι → ℝ)
    {Q : Matrix ν ν ℝ} (hQ : 0 ≤ Q) {t : ℝ} (ht : 0 ≤ t) :
    positiveExtension f (t • Q) = t • positiveExtension f Q := by
  unfold positiveExtension
  rw [matrix_sqrt_smul hQ ht, map_smul,
    integralLift_smul_nonneg f _ (Real.sqrt_nonneg t), Real.sq_sqrt ht]

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
local notation "E" => EuclideanSpace ℝ ν
local notation "op" => Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)

lemma Admissible.positiveExtension_kernel {f : E → ι → ℝ} (hf : Admissible f)
    {Q : Matrix ν ν ℝ} (hQ : 0 ≤ Q) {w : E} (hw : ‖w‖ = 1)
    (hk : op Q w = 0) {i : ι} (hi : 0 < f w i) : positiveExtension f Q i = 0 := by
  apply le_antisymm _ (hf.positiveExtension_nonneg Q i)
  apply le_of_not_gt
  intro hp
  obtain ⟨v, ⟨x, rfl⟩, hv, hx⟩ := (hf.positiveExtension_support hQ i).mp hp
  exact hf.orthogonal _ _ hw hv (matrix_image_orthogonal_kernel hQ.isSelfAdjoint hk x) i
    ⟨hi, hx⟩

end FullSupport

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

omit [DecidableEq ν] in
lemma blockCorner_selfAdjoint (e : W →ₗᵢ[ℝ] E) {A : M} (hA : IsSelfAdjoint A) :
    IsSelfAdjoint (blockCorner e A) := matrixEmbed_selfAdjoint e (matrixCompress_selfAdjoint e hA)
lemma blockCorner_kernel (e : W →ₗᵢ[ℝ] E) {c : E} (he : ∀ v, ⟪c,e v⟫ = 0) (A : M) :
    op (blockCorner e A) c = 0 := matrixEmbed_kernel e _ he
end MatrixBlocks
end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Support_FacetTangent
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine
open scoped BigOperators
section FacetTangent
variable {k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "W" => EuclideanSpace ℝ (Fin k)

omit [Fintype ι] in
lemma facetTangent_apply {I : Finset ι} (a : Fin (k+1) ≃ ↥I) (v : W) (j : Fin (k+1)) :
    facetTangent a v (a j).val = Fin.cases (-∑ j, v j) (fun j => v j) j := by
  simp [facetTangent]
omit [Fintype ι] in
lemma facetTangent_sum {I : Finset ι} (a : Fin (k+1) ≃ ↥I) (v : W) : ∑ i ∈ I, facetTangent a v i = 0 := by
  calc
    _ = ∑ i : ↥I, facetTangent a v i.val := (Finset.sum_coe_sort I _).symm
    _ = ∑ j : Fin (k+1), facetTangent a v (a j).val := (Equiv.sum_comp a _).symm
    _ = 0 := by simp only [facetTangent_apply,Fin.sum_univ_succ,Fin.cases_zero,Fin.cases_succ]; ring
end FacetTangent
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
local notation "op" => Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)

omit [DecidableEq ι] in
lemma Admissible.signedExtension_kernel_coordinate {f : E → ι → ℝ} (hf : Admissible f)
    {A : M} (hA : IsSelfAdjoint A) {c : E} (hc : ‖c‖ = 1) (hAc : op A c = 0)
    {i : ι} (hi : 0 < f c i) : signedExtension f A i = 0 := by
  obtain ⟨hp,hn⟩ := matrix_parts_kernel hA hAc
  simp only [signedExtension,Pi.sub_apply,
    hf.positiveExtension_kernel (CFC.posPart_nonneg A) hc hp hi,
    hf.positiveExtension_kernel (CFC.negPart_nonneg A) hc hn hi,sub_self]

lemma Admissible.localBlockModel_on_facet {f : E → ι → ℝ} (hf : Admissible f)
    {c : E} (hc : ‖c‖ = 1) (e : W →ₗᵢ[ℝ] E) (he : ∀ v, ⟪c,e v⟫ = 0)
    {I : Finset ι} (a : Fin (k+1) ≃ ↥I) (hI : ∀ i ∈ I, 0 < f c i)
    (D : W ≃L[ℝ] W) {A : M} (hA : IsSelfAdjoint A) {i : ι} (hi : i ∈ I) :
    localBlockModel f c e a D A i = blockScalar c A * f c i + facetTangent a (D (blockOff c e A)) i := by
  have hz := hf.signedExtension_kernel_coordinate (blockCorner_selfAdjoint e hA) hc
    (blockCorner_kernel e he A) (hI i hi)
  simp only [localBlockModel,Pi.add_apply,Pi.smul_apply,smul_eq_mul,hz,add_zero]

lemma Admissible.localBlockModel_sum_facet {f : E → ι → ℝ} (hf : Admissible f)
    {c : E} (hc : ‖c‖ = 1) (e : W →ₗᵢ[ℝ] E) (he : ∀ v, ⟪c,e v⟫ = 0)
    {I : Finset ι} (a : Fin (k+1) ≃ ↥I) (hIc : positiveSupport f c = I)
    (D : W ≃L[ℝ] W) {A : M} (hA : IsSelfAdjoint A) :
    ∑ i ∈ I, localBlockModel f c e a D A i = blockScalar c A := by
  have hp : ∀ i ∈ I, 0 < f c i := fun i hi => (mem_positiveSupport f c i).mp (hIc.symm ▸ hi)
  have hs : ∑ i ∈ I, f c i = 1 := by
    rw [← hf.sum_one c hc]
    apply Finset.sum_subset (Finset.subset_univ I)
    intro i _ hi
    apply le_antisymm _ (hf.nonneg c hc i)
    exact le_of_not_gt (fun h => hi (hIc ▸ (mem_positiveSupport f c i).mpr h))
  calc
    _ = ∑ i ∈ I, (blockScalar c A * f c i + facetTangent a (D (blockOff c e A)) i) :=
      Finset.sum_congr rfl (fun i hi => hf.localBlockModel_on_facet hc e he a hp D hA hi)
    _ = _ := by rw [Finset.sum_add_distrib,← Finset.mul_sum,hs,facetTangent_sum,mul_one,add_zero]

end LocalModel
end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_MatrixGeometry_Rank
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
section RankOne
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {ν ι : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν] [Fintype ι]
local notation "E" => EuclideanSpace ℝ ν
local notation "op" => Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)

omit [DecidableEq ν] [Nonempty ν] in
lemma Admissible.lift_smul {f : E → ι → ℝ} (hf : Admissible f) (v : E) (t : ℝ) :
    homogeneousLift f (t • v) = t ^ 2 • homogeneousLift f v := by
  rcases le_total 0 t with ht | ht
  · exact homogeneousLift_smul_nonneg f v ht
  · have h := homogeneousLift_smul_nonneg f v (neg_nonneg.mpr ht)
    rw [neg_smul, hf.lift_even, neg_sq] at h
    exact h

omit [Nonempty ν] in
lemma rankOne_mul_self (u : E) (hu : ‖u‖ = 1) : rankOne u * rankOne u = rankOne u := by
  apply (op).injective
  rw [map_mul]
  apply ContinuousLinearMap.ext
  intro x
  change op (rankOne u) (op (rankOne u) x) = op (rankOne u) x
  simp only [rankOne_action, inner_smul_right, real_inner_self_eq_norm_sq, hu, one_pow, mul_one]

omit [Nonempty ν] in
lemma rankOne_sqrt (u : E) (hu : ‖u‖ = 1) : CFC.sqrt (rankOne u) = rankOne u :=
  (CFC.sqrt_eq_iff _ _ (rankOne_nonneg u) (rankOne_nonneg u)).mpr
    (rankOne_mul_self u hu)

lemma Admissible.positiveExtension_rankOne {f : E → ι → ℝ} (hf : Admissible f)
    (u : E) (hu : ‖u‖ = 1) : positiveExtension f (rankOne u) = f u := by
  have hcoord (x : UnitSphere E) (i : ι) :
      homogeneousLift f (op (rankOne u) x) i = ⟪u, (x : E)⟫ ^ 2 * f u i := by
    rw [rankOne_action, hf.lift_smul, homogeneousLift_unit f hu]
    rfl
  have hm : (Fintype.card ν : ℝ) *
      ∫ x : UnitSphere E, ⟪u, (x : E)⟫ ^ 2 ∂sphereProbability E = 1 := by
    have hs := hf.positiveExtension_sum (rankOne_nonneg u)
    rw [rankOne_trace, hu, one_pow] at hs
    simp only [positiveExtension, rankOne_sqrt u hu, integralLift] at hs
    simp_rw [hcoord] at hs
    simp only [integral_mul_const, ← Finset.mul_sum] at hs
    rw [hf.sum_one u hu, mul_one] at hs
    exact hs
  ext i
  simp only [positiveExtension, rankOne_sqrt u hu, integralLift]
  simp_rw [hcoord]
  rw [integral_mul_const, ← mul_assoc, hm, one_mul]

end RankOne

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
-- module Solutions.OAIQ058_BK.Borsuk_Support_LocalMix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine
open scoped MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
section LocalMix
variable {k : ℕ} {ν ι : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν] [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ ν
local notation "W" => EuclideanSpace ℝ (Fin k)
local notation "M" => Matrix ν ν ℝ

omit [DecidableEq ν] [Nonempty ν] [DecidableEq ι] in
lemma Admissible.sum_on_support {f : E → ι → ℝ} (hf : Admissible f) {u : E} (hu : ‖u‖ = 1)
    {I : Finset ι} (hI : positiveSupport f u = I) : ∑ i ∈ I, f u i = 1 := by
  rw [← hf.sum_one u hu]
  apply Finset.sum_subset (Finset.subset_univ I)
  intro i _ hi
  apply le_antisymm _ (hf.nonneg u hu i)
  exact le_of_not_gt (fun h => hi (hI ▸ (mem_positiveSupport f u i).mpr h))

omit [DecidableEq ι] in
lemma Admissible.extension_on_positiveLine {f : E → ι → ℝ} (hf : Admissible f)
    {A : M} {u : E} (hu : ‖u‖ = 1) {lam : ℝ} (hl : 0 < lam)
    (hP : A⁺ = lam • rankOne u) {i : ι} (hi : 0 < f u i) :
    signedExtension f A i = lam * f u i := by
  have hn := hf.positiveExtension_kernel (CFC.negPart_nonneg A) hu
    (negPart_kernel_of_positiveLine hu hl hP) hi
  simp only [signedExtension,Pi.sub_apply,hn,sub_zero,hP,
    positiveExtension_smul_nonneg f (rankOne_nonneg u) hl.le,
    hf.positiveExtension_rankOne u hu,Pi.smul_apply,smul_eq_mul]

lemma Admissible.localBlockMix_sum {f : E → ι → ℝ} (hf : Admissible f)
    {A : M} (hA : IsSelfAdjoint A) {c u : E} (hc : ‖c‖ = 1) (hu : ‖u‖ = 1)
    (e : W →ₗᵢ[ℝ] E) (he : ∀ v, ⟪c,e v⟫ = 0)
    {I : Finset ι} (a : Fin (k+1) ≃ ↥I) (hIc : positiveSupport f c = I) (hIu : positiveSupport f u = I)
    (D : W ≃L[ℝ] W) {lam : ℝ} (hl : 0 < lam) (hP : A⁺ = lam • rankOne u) (t : ℝ) :
    ∑ i ∈ I, localBlockMix f c e a D t A i = (1-t)*lam + t*blockScalar c A := by
  have hF : ∑ i ∈ I, signedExtension f A i = lam := by
    calc
      _ = ∑ i ∈ I, lam * f u i := Finset.sum_congr rfl (fun i hi =>
        hf.extension_on_positiveLine hu hl hP ((mem_positiveSupport f u i).mp (hIu.symm ▸ hi)))
      _ = _ := by rw [← Finset.mul_sum,hf.sum_on_support hu hIu,mul_one]
  simp only [localBlockMix,Pi.add_apply,Pi.smul_apply,smul_eq_mul,Finset.sum_add_distrib,
    ← Finset.mul_sum,hF,hf.localBlockModel_sum_facet hc e he a hIc D hA]

lemma Admissible.localBlockMix_ne_zero_oai {f : E → ι → ℝ} (hf : Admissible f)
    {A : M} (hA : IsSelfAdjoint A) {c u : E} (hc : ‖c‖ = 1) (hu : ‖u‖ = 1)
    (e : W →ₗᵢ[ℝ] E) (he : ∀ v, ⟪c,e v⟫ = 0)
    {I : Finset ι} (a : Fin (k+1) ≃ ↥I) (hIc : positiveSupport f c = I) (hIu : positiveSupport f u = I)
    (D : W ≃L[ℝ] W) {lam : ℝ} (hl : 0 < lam) (hP : A⁺ = lam • rankOne u)
    (ha : 0 < blockScalar c A) {t : ℝ} (ht : t ∈ Set.Icc 0 1) : localBlockMix f c e a D t A ≠ 0 := by
  intro hz
  have hh := hf.localBlockMix_sum hA hc hu e he a hIc hIu D hl hP t
  rw [hz] at hh
  simp only [Pi.zero_apply,Finset.sum_const_zero] at hh
  have hp : 0 < (1-t)*lam + t*blockScalar c A := by
    by_cases ht0 : t = 0
    · simpa [ht0] using hl
    · exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr ht.2) hl.le)
        (mul_pos (lt_of_le_of_ne ht.1 (Ne.symm ht0)) ha)
  linarith

end LocalMix
end BorsukNine

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.BorsukNine.Admissible.localBlockMix_ne_zero_oai.{u_1, u_2} := @OAI.BorsukNine.Admissible.localBlockMix_ne_zero_oai.{u_1, u_2}
