-- Prove2me | solution 1 for OAI.BorsukNine.Admissible.localBlockMix_hit
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T20:54:00.747001+00:00
-- url     : https://prove2.me/submissions/e4632bfb-08e5-408f-a414-9c39b13a7d3a

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

end HemisphereChart
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
open scoped RealInnerProductSpace Topology
open Filter Set
section NegativeQuadratic
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace X]
omit [FiniteDimensional ℝ E] in
lemma negativeQuadratic_pos_sub {B : E →L[ℝ] E} (hB : NegativeQuadratic B)
    {v : E} (hv : v ≠ 0) {lam : ℝ} (hl : 0 < lam) : 0 < ⟪v,lam • v - B v⟫ := by
  rw [inner_sub_right,real_inner_smul_right,real_inner_self_eq_norm_sq]
  exact sub_pos.mpr ((hB v hv).trans_le (mul_nonneg hl.le (sq_nonneg _)))
end NegativeQuadratic
end BorsukNine

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
lemma blockCorner_kernel (e : W →ₗᵢ[ℝ] E) {c : E} (he : ∀ v, ⟪c,e v⟫ = 0) (A : M) :
    op (blockCorner e A) c = 0 := matrixEmbed_kernel e _ he
lemma blockCorner_of_kernel (e : W →ₗᵢ[ℝ] E) {c : E}
    (hes : ∀ u, ⟪c,u⟫ = 0 → ∃ v, e v = u) {A : M} (hA : IsSelfAdjoint A) (hAc : op A c = 0) :
    blockCorner e A = A := by
  apply matrixEmbed_compress e hA
  rintro _ ⟨x,rfl⟩
  exact hes _ (matrix_image_orthogonal_kernel hA hAc x)

lemma blockOff_eigenvector {c u : E} (e : W →ₗᵢ[ℝ] E) (hc : ‖c‖ = 1)
    (he : ∀ v, ⟪c,e v⟫ = 0) (hes : ∀ u, ⟪c,u⟫ = 0 → ∃ v, e v = u)
    {A : M} {lam : ℝ} (_hu : ‖u‖ = 1) (hcu : 0 < ⟪c,u⟫) (hAu : op A u = lam • u) :
    blockOff c e A = lam • hemisphereInverse c e u - op (matrixCompress e A) (hemisphereInverse c e u) := by
  let v := hemisphereInverse c e u
  have heq : c + e v = ⟪c,u⟫⁻¹ • u := by
    rw [show v = hemisphereInverse c e u from rfl,hemisphereInverse,map_smul,
      frame_decomposition c e hc he hes,smul_sub,smul_smul,inv_mul_cancel₀ (ne_of_gt hcu),one_smul]
    abel
  have hae : op A (c + e v) = lam • (c + e v) := by
    rw [heq,map_smul,hAu,smul_comm]
  have hb := congrArg e.toContinuousLinearMap.adjoint hae
  rw [map_add,map_add,map_smul,map_add,adjoint_normal c e he,zero_add] at hb
  rw [adjoint_isometry_apply,← matrixCompress_action] at hb
  exact eq_sub_iff_add_eq.mpr hb
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

lemma positive_inner_convex {v x y : E} (hx : 0 < ⟪v,x⟫) (hy : 0 < ⟪v,y⟫)
    {t : ℝ} (ht : t ∈ Set.Icc 0 1) : 0 < ⟪v,(1-t) • x + t • y⟫ := by
  simp only [inner_add_right,real_inner_smul_right]
  by_cases ht0 : t = 0
  · simpa [ht0] using hx
  · exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr ht.2) hx.le)
      (mul_pos (lt_of_le_of_ne ht.1 (Ne.symm ht0)) hy)

lemma regular_mixed_zero (D : E ≃L[ℝ] E) {g : E → E} {v b : E} {lam t : ℝ}
    (hp : v ≠ 0 → 0 < ⟪v,D.symm (g v)⟫) (hb : v ≠ 0 → 0 < ⟪v,b⟫)
    (hl : 0 < lam) (ht : t ∈ Set.Icc 0 1)
    (hz : (1-t) • (lam • g v) + t • D b = 0) : v = 0 := by
  by_contra hv
  have hh := positive_inner_convex (by simpa only [real_inner_smul_right] using mul_pos hl (hp hv)) (hb hv) ht
    (v := v) (x := lam • D.symm (g v))
  have he := congrArg D.symm hz
  simp only [map_add,map_smul,D.symm_apply_apply,map_zero] at he
  rw [he,inner_zero_right] at hh
  exact (lt_irrefl (0:ℝ)) hh
end LocalRegular
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

omit [Nonempty ν] in
lemma block_parts {c : E} (e : W →ₗᵢ[ℝ] E) (hc : ‖c‖ = 1)
    (he : ∀ v, ⟪c,e v⟫ = 0) (hes : ∀ u, ⟪c,u⟫ = 0 → ∃ v, e v = u)
    {A : M} (hA : IsSelfAdjoint A) (hb : blockOff c e A = 0)
    (ha : 0 ≤ blockScalar c A) (hC : blockCorner e A ≤ 0) :
    A⁺ = blockScalar c A • rankOne c ∧ A⁻ = -blockCorner e A := by
  have hk : op (-blockCorner e A) c = 0 := by
    rw [map_neg,neg_apply,blockCorner_kernel e he,neg_zero]
  have hp := rankOne_split_parts (neg_nonneg.mpr hC) hk ha (show (0:ℝ) ≤ 1 by norm_num)
  have heq : A = blockScalar c A • rankOne c - (1:ℝ) • (-blockCorner e A) := by
    rw [one_smul,sub_neg_eq_add]
    exact block_decomposition e hc he hes hA hb
  rw [← heq] at hp
  simpa only [one_smul] using hp

lemma Admissible.block_extension {f : E → ι → ℝ} (hf : Admissible f)
    {c : E} (e : W →ₗᵢ[ℝ] E) (hc : ‖c‖ = 1)
    (he : ∀ v, ⟪c,e v⟫ = 0) (hes : ∀ u, ⟪c,u⟫ = 0 → ∃ v, e v = u)
    {A : M} (hA : IsSelfAdjoint A) (hb : blockOff c e A = 0)
    (ha : 0 ≤ blockScalar c A) (hC : blockCorner e A ≤ 0) :
    signedExtension f A = blockScalar c A • f c + signedExtension f (blockCorner e A) := by
  obtain ⟨hp,hn⟩ := block_parts e hc he hes hA hb ha hC
  have hCp : (blockCorner e A)⁺ = 0 := (CFC.posPart_eq_zero_iff _ (blockCorner_selfAdjoint e hA)).mpr hC
  have hCn : (blockCorner e A)⁻ = -blockCorner e A := by
    have h := CFC.posPart_sub_negPart (blockCorner e A) (blockCorner_selfAdjoint e hA)
    rw [hCp,zero_sub] at h
    exact (neg_eq_iff_eq_neg.mp h)
  ext i
  simp only [signedExtension,Pi.sub_apply,hp,hn,hCp,hCn,positiveExtension_smul_nonneg f (rankOne_nonneg c) ha,
    hf.positiveExtension_rankOne c hc,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  have hz : positiveExtension f (0:M) = 0 := by
    simpa only [zero_smul] using positiveExtension_smul_nonneg f (Q := (0:M)) le_rfl (t := 0) le_rfl
  rw [hz]
  simp only [Pi.zero_apply,sub_eq_add_neg,zero_add]
end BlockParts
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

end BlockLine
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

lemma Admissible.localBlockModel_eq_of_positiveLine {f : E → ι → ℝ} (hf : Admissible f)
    {A : M} (hA : IsSelfAdjoint A) {c : E} (hc : ‖c‖ = 1) (e : W →ₗᵢ[ℝ] E)
    (he : ∀ v, ⟪c,e v⟫ = 0) (hes : ∀ u, ⟪c,u⟫ = 0 → ∃ v, e v = u)
    {I : Finset ι} (a : Fin (k+1) ≃ ↥I) (D : W ≃L[ℝ] W)
    {lam : ℝ} (hl : 0 < lam) (hP : A⁺ = lam • rankOne c) :
    localBlockModel f c e a D A = signedExtension f A := by
  have hb := blockOff_positiveLine e hA hc he hl hP
  have hC : blockCorner e A ≤ 0 := by rw [blockCorner_positiveLine e hA hc he hes hl hP]; exact neg_nonpos.mpr (CFC.negPart_nonneg A)
  have ha : 0 ≤ blockScalar c A := by rw [blockScalar_positiveLine hA hc hl hP]; exact hl.le
  rw [hf.block_extension e hc he hes hA hb ha hC]
  simp only [localBlockModel,hb,map_zero,add_zero]

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

lemma Admissible.localBlockMix_tangent_zero {f : E → ι → ℝ} (hf : Admissible f)
    {A : M} (hA : IsSelfAdjoint A) {c u : E} (hc : ‖c‖ = 1) (hu : ‖u‖ = 1)
    (e : W →ₗᵢ[ℝ] E) (he : ∀ v, ⟪c,e v⟫ = 0) (_hes : ∀ u, ⟪c,u⟫ = 0 → ∃ v, e v = u)
    {I : Finset ι} (a : Fin (k+1) ≃ ↥I) (hIc : positiveSupport f c = I) (hIu : positiveSupport f u = I)
    (D : W ≃L[ℝ] W) {lam : ℝ} (hl : 0 < lam) (hP : A⁺ = lam • rankOne u) (_hcu : 0 < ⟪c,u⟫)
    (_hB : NegativeQuadratic (Matrix.toEuclideanCLM (𝕜 := ℝ) (matrixCompress e A)))
    (_hreg : hemisphereInverse c e u ≠ 0 →
      0 < ⟪hemisphereInverse c e u,D.symm (facetTail a (f u - f c))⟫)
    {y : ι → ℝ} {rho d t : ℝ} (hyi : ∀ i ∈ I, y i = rho * f c i)
    (_ht : t ∈ Set.Icc 0 1) (hM : localBlockMix f c e a D t A = d • y) :
    (1-t) • (lam • facetTail a (f u - f c)) + t • D (blockOff c e A) = 0 := by
  have hp : ∀ i ∈ I, 0 < f c i := fun i hi => (mem_positiveSupport f c i).mp (hIc.symm ▸ hi)
  have hpu : ∀ i ∈ I, 0 < f u i := fun i hi => (mem_positiveSupport f u i).mp (hIu.symm ▸ hi)
  have hs : (1-t)*lam+t*blockScalar c A = d*rho := by
    rw [← hf.localBlockMix_sum hA hc hu e he a hIc hIu D hl hP t,hM]
    simp only [Pi.smul_apply,smul_eq_mul]
    calc
      _ = ∑ i ∈ I, d*(rho*f c i) := Finset.sum_congr rfl (fun i hi => by rw [hyi i hi])
      _ = _ := by rw [← Finset.mul_sum,← Finset.mul_sum,hf.sum_on_support hc hIc,mul_one]
  apply PiLp.ext
  intro j
  have hi := (a j.succ).property
  have hh := congrFun hM (a j.succ).val
  simp only [localBlockMix,Pi.add_apply,Pi.smul_apply,smul_eq_mul,
    hf.extension_on_positiveLine hu hl hP (hpu _ hi),
    hf.localBlockModel_on_facet hc e he a hp D hA hi,facetTangent_apply,Fin.cases_succ,hyi _ hi] at hh
  change (1-t)*(lam*(f u (a j.succ).val - f c (a j.succ).val)) + t*(D (blockOff c e A)) j = 0
  nlinarith [congrArg (fun x : ℝ => x * f c (a j.succ).val) hs]

lemma Admissible.localBlockMix_hit_oai {f : E → ι → ℝ} (hf : Admissible f)
    {A : M} (hA : IsSelfAdjoint A) {c u : E} (hc : ‖c‖ = 1) (hu : ‖u‖ = 1)
    (e : W →ₗᵢ[ℝ] E) (he : ∀ v, ⟪c,e v⟫ = 0) (hes : ∀ u, ⟪c,u⟫ = 0 → ∃ v, e v = u)
    {I : Finset ι} (a : Fin (k+1) ≃ ↥I) (hIc : positiveSupport f c = I) (hIu : positiveSupport f u = I)
    (D : W ≃L[ℝ] W) {lam : ℝ} (hl : 0 < lam) (hP : A⁺ = lam • rankOne u) (hcu : 0 < ⟪c,u⟫)
    (hB : NegativeQuadratic (Matrix.toEuclideanCLM (𝕜 := ℝ) (matrixCompress e A)))
    (hreg : hemisphereInverse c e u ≠ 0 →
      0 < ⟪hemisphereInverse c e u,D.symm (facetTail a (f u - f c))⟫)
    {y : ι → ℝ} {rho d t : ℝ} (hyi : ∀ i ∈ I, y i = rho * f c i)
    (ht : t ∈ Set.Icc 0 1) (hM : localBlockMix f c e a D t A = d • y) :
    u = c ∧ localBlockMix f c e a D t A = signedExtension f A := by
  have hz := hf.localBlockMix_tangent_zero hA hc hu e he hes a hIc hIu D hl hP hcu hB hreg hyi ht hM
  have hb : hemisphereInverse c e u ≠ 0 → 0 < ⟪hemisphereInverse c e u,blockOff c e A⟫ := by
    intro hv
    rw [blockOff_eigenvector e hc he hes hu hcu (positiveLine_eigenvector hA hu hl hP)]
    exact negativeQuadratic_pos_sub hB hv hl
  have hv : hemisphereInverse c e u = 0 := regular_mixed_zero D (g := fun _ : W => facetTail a (f u-f c)) (v := hemisphereInverse c e u) (b := blockOff c e A) hreg hb hl ht hz
  have huc : u = c := by
    have hh := hemisphereChart_inverse c e hc he hes hu hcu
    rw [hv] at hh
    simpa only [hemisphereChart,SimplicialChains.unitRadial,map_zero,add_zero,hc,inv_one,one_smul] using hh.symm
  refine ⟨huc,?_⟩
  have hm := hf.localBlockModel_eq_of_positiveLine hA hc e he hes a D hl (huc ▸ hP)
  rw [localBlockMix,hm,← add_smul,sub_add_cancel,one_smul]
end LocalMix
end BorsukNine

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.BorsukNine.Admissible.localBlockMix_hit_oai.{u_1, u_2} := @OAI.BorsukNine.Admissible.localBlockMix_hit_oai.{u_1, u_2}
