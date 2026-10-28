-- Prove2me | solution 1 for OAI.BorsukNine.Admissible.original_ray_level
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T21:02:35.528904+00:00
-- url     : https://prove2.me/submissions/d7efcb34-de7e-4875-ad99-bce6d8def073

import Mathlib
import Definitions.Def_OAIQ058B000
import Theorems.Thm_OAI_BorsukNine_Admissible_mixedHomotopy_zero

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

lemma blockVector_ray {I : Finset ι} {lam mu t : ℝ} (_hl : 0 < lam) (_hm : 0 < mu)
    (hlm : lam + mu = 1) (_ht : 0 < t) {a r : ι → ℝ}
    (hao : ∀ i ∉ I, a i = 0) (hro : ∀ i ∉ I, r i = 0)
    (has : ∑ i, a i = 1) (hrs : ∑ i, r i = 1)
    {b z : EuclideanSpace ℝ ↥(Iᶜ : Finset ι)} (hbs : ∑ i, b i = 1) (hzs : ∑ i, z i = 1)
    (he : blockVector I lam a mu b = t • blockVector I (1/2:ℝ) r (1/2:ℝ) z) :
    t = 1 ∧ lam = 1/2 ∧ mu = 1/2 ∧ a = r ∧ b = z := by
  have hei (i : ι) (hi : i ∈ I) : lam * a i = t * ((1/2:ℝ) * r i) := by
    have h := congrArg (fun v : EuclideanSpace ℝ ι => v i) he
    simpa only [PiLp.smul_apply,smul_eq_mul,blockVector_in _ _ _ _ _ hi] using h
  have heo (i : ↥(Iᶜ : Finset ι)) : -mu * b i = t * (-(1/2:ℝ) * z i) := by
    have h := congrArg (fun v : EuclideanSpace ℝ ι => v i.val) he
    simpa only [PiLp.smul_apply,smul_eq_mul,blockVector_out] using h
  have hia : ∑ i ∈ I, a i = 1 := by
    rw [← has]; exact Finset.sum_subset (Finset.subset_univ I) (fun i _ hi => hao i hi)
  have hir : ∑ i ∈ I, r i = 1 := by
    rw [← hrs]; exact Finset.sum_subset (Finset.subset_univ I) (fun i _ hi => hro i hi)
  have hl' : lam = t*(1/2:ℝ) := by
    have hs := Finset.sum_congr (s₁ := I) (rfl) hei
    simpa only [← Finset.mul_sum,hia,hir,mul_one] using hs
  have hm' : -mu = t*(-(1/2:ℝ)) := by
    have hs := congrArg (fun v : ↥(Iᶜ : Finset ι) → ℝ => ∑ i, v i) (funext heo)
    simpa only [← Finset.mul_sum,hbs,hzs,mul_one] using hs
  have ht1 : t = 1 := by linarith
  have hl2 : lam = 1/2 := by linarith
  have hm2 : mu = 1/2 := by linarith
  refine ⟨ht1,hl2,hm2,?_,?_⟩
  · funext i
    by_cases hi : i ∈ I
    · have h := hei i hi; rw [ht1,hl2] at h; linarith
    · rw [hao i hi,hro i hi]
  · apply PiLp.ext
    intro i
    have h := heo i; rw [ht1,hm2] at h; linarith
end BlockVector
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
-- module Solutions.OAIQ058_BK.Borsuk_MatrixGeometry_MatrixTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
section MatrixTransport
variable {ν : Type*} [Fintype ν] [DecidableEq ν]
local notation "E" => EuclideanSpace ℝ ν
local notation "M" => Matrix ν ν ℝ
local notation "op" => Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)

lemma matrixConjugate_action (e : E ≃ₗᵢ[ℝ] E) (A : M) (v : E) :
    op (matrixConjugate e A) v = e (op A (e.symm v)) := by
  simp only [matrixConjugate,StarAlgEquiv.trans_apply,StarAlgEquiv.apply_symm_apply,
    LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]

lemma matrixConjugate_involutive {e : E ≃ₗᵢ[ℝ] E}
    (he : ∀ v, e (e v) = v) (A : M) : matrixConjugate e (matrixConjugate e A) = A := by
  have hes : ∀ v, e.symm v = e v := by intro v; apply e.injective; simp [he]
  apply (Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)).injective
  change op (matrixConjugate e (matrixConjugate e A)) = op A
  apply ContinuousLinearMap.ext
  intro v
  simp only [matrixConjugate_action,hes,he]

end MatrixTransport
end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_MatrixGeometry_MatrixReflection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
section MatrixReflection
variable {ν : Type*} [Fintype ν] [DecidableEq ν]
local notation "E" => EuclideanSpace ℝ ν

omit [DecidableEq ν] in
lemma householder_involutive (c u : E) : Function.Involutive (householder c u) :=
  (Submodule.span ℝ {c+u}).reflection_involutive

end MatrixReflection
end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_MatrixGeometry_FibreTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator
section FibreTransport
variable {ν : Type*} [Fintype ν] [DecidableEq ν]
local notation "E" => EuclideanSpace ℝ ν
local notation "M" => Matrix ν ν ℝ

lemma fibreTransport_self (c u : E) (Q : M) : fibreTransport c u u Q = Q :=
  matrixConjugate_involutive (householder_involutive c u) Q

end FibreTransport
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

end Chambers
end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Support_ChamberPath
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace
section ChamberPath
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma chamberPath_zero (c u : E) (hu : ‖u‖ = 1) : chamberPath c u 0 = u := by
  simp [chamberPath,hu]

end ChamberPath
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

lemma Admissible.signedExtension_kernel {f : E → ι → ℝ} (hf : Admissible f)
    {A : Matrix ν ν ℝ} (hA : IsSelfAdjoint A) {w : E} (hw : ‖w‖ = 1)
    (hk : op A w = 0) : ∃ i, signedExtension f A i = 0 := by
  obtain ⟨i, hi⟩ := hf.support_nonempty hw
  have hi' := (mem_positiveSupport f w i).mp hi
  obtain ⟨hp, hn⟩ := matrix_parts_kernel hA hk
  refine ⟨i, ?_⟩
  simp only [signedExtension, Pi.sub_apply,
    hf.positiveExtension_kernel (CFC.posPart_nonneg A) hw hp hi',
    hf.positiveExtension_kernel (CFC.negPart_nonneg A) hw hn hi', sub_self]

lemma Admissible.signedExtension_kernel_eq_zero {f : E → ι → ℝ} (hf : Admissible f)
    {A : Matrix ν ν ℝ} (hA : IsSelfAdjoint A) (hs : ∀ i, signedExtension f A i ≠ 0)
    {w : E} (hk : op A w = 0) : w = 0 := by
  by_contra hw
  have hunit : ‖‖w‖⁻¹ • w‖ = 1 := by simp [norm_smul, norm_inv, hw]
  have hk' : op A (‖w‖⁻¹ • w) = 0 := by rw [map_smul, hk, smul_zero]
  obtain ⟨i, hi⟩ := hf.signedExtension_kernel hA hunit hk'
  exact hs i hi

lemma Admissible.signedExtension_fullSupport {f : E → ι → ℝ} (hf : Admissible f)
    {A : Matrix ν ν ℝ} (hA : IsSelfAdjoint A) (hs : ∀ i, signedExtension f A i ≠ 0) :
    IsUnit A := by
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro u v huv
  have hz : op A (WithLp.toLp 2 u - WithLp.toLp 2 v) = 0 := by
    rw [map_sub, Matrix.toEuclideanCLM_toLp, Matrix.toEuclideanCLM_toLp, huv, sub_self]
  have h := sub_eq_zero.mp (hf.signedExtension_kernel_eq_zero hA hs hz)
  exact WithLp.toLp_injective 2 h

end FullSupport

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

omit [Nonempty ν] in
lemma fibreHomotopy_zero (f : E → ι → ℝ) (I : Finset ι) (c : E)
    (g : M → EuclideanSpace ℝ ↥(Iᶜ : Finset ι)) {u : E} (hu : ‖u‖ = 1) (Q : M) :
    fibreHomotopy f I c g 0 u Q = negativeCoordinates f I Q := by
  simp only [fibreHomotopy,zero_smul,add_zero,transportedFibre,chamberPath_zero c u hu,
    fibreTransport_self]

end FibreHomotopy
end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Support_SpectralSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
section SpectralSupport
variable {ν ι : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν] [Fintype ι]
local notation "E" => EuclideanSpace ℝ ν
local notation "op" => Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)

lemma Admissible.signedExtension_pos_iff {f : E → ι → ℝ} (hf : Admissible f)
    (A : Matrix ν ν ℝ) (i : ι) :
    0 < signedExtension f A i ↔ 0 < positiveExtension f A⁺ i := by
  have hp := hf.positiveExtension_nonneg A⁺ i
  have hn := hf.positiveExtension_nonneg A⁻ i
  have hpn := hf.positiveExtension_orthogonal (CFC.posPart_nonneg A)
    (CFC.negPart_nonneg A) (CFC.posPart_mul_negPart A) i
  change 0 < positiveExtension f A⁺ i - positiveExtension f A⁻ i ↔ _
  constructor
  · intro h; linarith
  · intro h
    have hz := (mul_eq_zero.mp hpn).resolve_left (ne_of_gt h)
    rwa [hz,sub_zero]

lemma Admissible.signedExtension_neg_iff {f : E → ι → ℝ} (hf : Admissible f)
    (A : Matrix ν ν ℝ) (i : ι) :
    signedExtension f A i < 0 ↔ 0 < positiveExtension f A⁻ i := by
  have hp := hf.positiveExtension_nonneg A⁺ i
  have hn := hf.positiveExtension_nonneg A⁻ i
  have hpn := hf.positiveExtension_orthogonal (CFC.posPart_nonneg A)
    (CFC.negPart_nonneg A) (CFC.posPart_mul_negPart A) i
  change positiveExtension f A⁺ i - positiveExtension f A⁻ i < 0 ↔ _
  constructor
  · intro h; linarith
  · intro h
    have hz := (mul_eq_zero.mp hpn).resolve_right (ne_of_gt h)
    rw [hz,zero_sub]
    exact neg_neg_of_pos h

lemma Admissible.signedExtension_positive_support {f : E → ι → ℝ} (hf : Admissible f)
    (A : Matrix ν ν ℝ) (i : ι) :
    0 < signedExtension f A i ↔ ∃ v : E,
      v ∈ LinearMap.range (op A⁺).toLinearMap ∧ ‖v‖ = 1 ∧ 0 < f v i := by
  rw [hf.signedExtension_pos_iff,hf.positiveExtension_support (CFC.posPart_nonneg A)]

lemma Admissible.signedExtension_range_labels {f : E → ι → ℝ} (hf : Admissible f)
    {A : Matrix ν ν ℝ} {I : Finset ι}
    (hI : ∀ i ∉ I, signedExtension f A i ≤ 0)
    {v : E} (hv : v ∈ LinearMap.range (op A⁺).toLinearMap) (hvn : ‖v‖ = 1)
    {i : ι} (hi : i ∉ I) : f v i = 0 := by
  apply le_antisymm _ (hf.nonneg v hvn i)
  by_contra hn
  have hp : 0 < f v i := lt_of_not_ge hn
  exact (not_lt_of_ge (hI i hi)) ((hf.signedExtension_positive_support A i).mpr ⟨v,hv,hvn,hp⟩)

omit [DecidableEq ν] [Nonempty ν] in

lemma subspace_eq_span_of_inner_separates (W : Submodule ℝ E) (w u : E)
    (hu : u ∈ W) (huw : ⟪w,u⟫ ≠ 0)
    (hsep : ∀ v ∈ W, ⟪w,v⟫ = 0 → v = 0) : W = Submodule.span ℝ {u} := by
  apply le_antisymm
  · intro v hv
    have hz : v - (⟪w,v⟫ / ⟪w,u⟫) • u = 0 := hsep _
      (W.sub_mem hv (W.smul_mem _ hu)) (by rw [inner_sub_right,inner_smul_right]; field_simp; ring)
    rw [sub_eq_zero] at hz
    rw [hz]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton u))
  · exact Submodule.span_le.mpr (by simpa using hu)

lemma Admissible.positive_range_separated {f : E → ι → ℝ} (hf : Admissible f)
    {A : Matrix ν ν ℝ} {I : Finset ι} {w : E} (hw : ‖w‖ = 1)
    (hwi : ∀ i ∈ I, 0 < f w i)
    (hI : ∀ i ∉ I, signedExtension f A i ≤ 0)
    {v : E} (hv : v ∈ LinearMap.range (op A⁺).toLinearMap) (hwv : ⟪w,v⟫ = 0) : v = 0 := by
  by_contra hn
  let u : E := ‖v‖⁻¹ • v
  have hu : ‖u‖ = 1 := by simp [u,norm_smul,norm_inv,hn]
  have hur : u ∈ LinearMap.range (op A⁺).toLinearMap := Submodule.smul_mem _ _ hv
  obtain ⟨i,hi⟩ := hf.support_nonempty hu
  have hip : 0 < f u i := by simpa [positiveSupport] using hi
  by_cases hiI : i ∈ I
  · exact hf.orthogonal w u hw hu (by simp [u,inner_smul_right,hwv]) i ⟨hwi i hiI,hip⟩
  · have hz := hf.signedExtension_range_labels hI hur hu hiI
    rw [hz] at hip
    exact (lt_irrefl 0) hip

end SpectralSupport
end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_MatrixGeometry_RankPreimage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
section RankOnePreimage
variable {ν ι : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν] [Fintype ι]
local notation "E" => EuclideanSpace ℝ ν
local notation "op" => Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)

omit [Nonempty ν] in
lemma symmetric_inner_action {A : Matrix ν ν ℝ} (hA : IsSelfAdjoint A) (u v : E) :
    ⟪u,op A v⟫ = ⟪op A u,v⟫ := by
  rw [← ContinuousLinearMap.adjoint_inner_right,← ContinuousLinearMap.star_eq_adjoint,
    ← map_star,hA.star_eq]

omit [Nonempty ν] in
lemma symmetric_eq_rankOne_of_range {A : Matrix ν ν ℝ} (hA : IsSelfAdjoint A)
    {u : E} (hu : ‖u‖ = 1)
    (hR : LinearMap.range (op A).toLinearMap ≤ Submodule.span ℝ {u}) :
    A = ⟪u,op A u⟫ • rankOne u := by
  have he (v : E) : op A v = ⟪u,op A v⟫ • u := by
    obtain ⟨t,ht⟩ := Submodule.mem_span_singleton.mp (hR (LinearMap.mem_range_self _ v))
    change t • u = (op A) v at ht
    rw [← ht,inner_smul_right,real_inner_self_eq_norm_sq,hu,one_pow,mul_one]
  have hscalar (v : E) : ⟪u,op A v⟫ = ⟪u,op A u⟫ * ⟪u,v⟫ := by
    calc
      ⟪u,op A v⟫ = ⟪op A u,v⟫ := symmetric_inner_action hA u v
      _ = ⟪u,op A u⟫ * ⟪u,v⟫ := by
        conv_lhs => rw [he u]
        simp only [inner_smul_left,conj_trivial]
  apply (Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)).injective
  change op A = op (⟪u,op A u⟫ • rankOne u)
  rw [map_smul]
  apply ContinuousLinearMap.ext
  intro v
  rw [smul_apply,rankOne_action,smul_smul,← hscalar,← he]

lemma Admissible.signedExtension_positive_rankOne {f : E → ι → ℝ} (hf : Admissible f)
    {A : Matrix ν ν ℝ} {I : Finset ι} {w : E} (hw : ‖w‖ = 1)
    (hwi : ∀ i ∈ I, 0 < f w i)
    (hI : ∀ i ∉ I, signedExtension f A i ≤ 0)
    (hpos : ∃ i, 0 < signedExtension f A i) :
    ∃ u : E, ‖u‖ = 1 ∧ ∃ lam : ℝ, 0 < lam ∧ A⁺ = lam • rankOne u := by
  obtain ⟨i,hi⟩ := hpos
  obtain ⟨u,hur,hu,hui⟩ := (hf.signedExtension_positive_support A i).mp hi
  have hwu : ⟪w,u⟫ ≠ 0 := by
    intro he
    have hz := hf.positive_range_separated hw hwi hI hur he
    simp [hz] at hu
  have hr : LinearMap.range (op A⁺).toLinearMap = Submodule.span ℝ {u} :=
    subspace_eq_span_of_inner_separates _ w u hur hwu
      (fun v hv horth => hf.positive_range_separated hw hwi hI hv horth)
  have hP := symmetric_eq_rankOne_of_range (CFC.posPart_nonneg A).isSelfAdjoint hu hr.le
  let lam : ℝ := ⟪u,op A⁺ u⟫
  have hlam : 0 ≤ lam := by
    change 0 ≤ ⟪u,op A⁺ u⟫
    rw [← sqrt_action_norm_sq A⁺ (CFC.posPart_nonneg A) u]
    positivity
  have hlam0 : lam ≠ 0 := by
    intro hz
    have hp0 : A⁺ = 0 := by simpa only [lam,hz,zero_smul] using hP
    obtain ⟨v,hv⟩ := hur
    rw [hp0,map_zero] at hv
    have hu0 : u = 0 := by simpa using hv.symm
    simp [hu0] at hu
  exact ⟨u,hu,lam,lt_of_le_of_ne hlam (Ne.symm hlam0),hP⟩

lemma Admissible.signedExtension_line_labels {f : E → ι → ℝ} (hf : Admissible f)
    {A : Matrix ν ν ℝ} {u : E} (hu : ‖u‖ = 1)
    {lam : ℝ} (hlam : 0 < lam) (he : A⁺ = lam • rankOne u) (i : ι) :
    0 < signedExtension f A i ↔ 0 < f u i := by
  rw [hf.signedExtension_pos_iff,he,
    positiveExtension_smul_nonneg f (rankOne_nonneg u) hlam.le,
    hf.positiveExtension_rankOne u hu,Pi.smul_apply,smul_eq_mul]
  exact mul_pos_iff_of_pos_left hlam

end RankOnePreimage
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

omit [Nonempty ν] in
lemma lineRepresentative_inner_pos {w : E} {A : M} (hA : HasPositiveLine A)
    (hAw : op A⁺ w ≠ 0) : 0 < ⟪w,lineRepresentative w A⟫ := by
  obtain ⟨u,hu,lam,hl,he⟩ := hA
  have hi : ⟪u,w⟫ ≠ 0 := by
    intro hz
    apply hAw
    rw [he,map_smul,smul_apply,rankOne_action,hz,zero_smul,smul_zero]
  have hp : 0 < ⟪w,op A⁺ w⟫ := by
    rw [he,map_smul,smul_apply,rankOne_action,inner_smul_right,
      inner_smul_right,real_inner_comm w u]
    exact mul_pos hl (mul_self_pos.mpr (by simpa only [real_inner_comm] using hi))
  rw [lineRepresentative,inner_smul_right]
  exact mul_pos (inv_pos.mpr (norm_pos_iff.mpr hAw)) hp

lemma unit_rankOne_inner_nonzero {A : M} (_hA : HasPositiveLine A) {w u : E}
    (hu : ‖u‖ = 1) {lam : ℝ} (hl : 0 < lam) (he : A⁺ = lam • rankOne u)
    (hwu : ⟪w,u⟫ ≠ 0) : op A⁺ w ≠ 0 := by
  rw [he,map_smul,smul_apply,rankOne_action]
  apply smul_ne_zero (ne_of_gt hl)
  apply smul_ne_zero (by simpa only [real_inner_comm] using hwu)
  intro hz
  simp [hz] at hu

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

lemma negativeFibre_mem {A : M} (hA : HasPositiveLine A) {w : E}
    (hAw : op A⁺ w ≠ 0) (hm : 0 < Matrix.trace A⁻) :
    negativeFibre A ∈ matrixFibre (lineRepresentative w A) := by
  have hu := lineRepresentative_norm hAw
  have hl := hasPositiveLine_trace_pos hA
  have he := positive_line_representative hA hAw
  refine ⟨smul_nonneg (inv_nonneg.mpr hm.le) (CFC.negPart_nonneg A),?_,?_⟩
  · rw [negativeFibre,Matrix.trace_smul,smul_eq_mul,inv_mul_cancel₀ (ne_of_gt hm)]
  · rw [negativeFibre,map_smul,smul_apply,
      negPart_kernel_of_positiveLine hu hl he,smul_zero]

end NegativeFibre
end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Support_PurityChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator Topology
open Set
section PurityChart
variable {ν ι : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν] [Fintype ι]
local notation "E" => EuclideanSpace ℝ ν
local notation "M" => Matrix ν ν ℝ

omit [Fintype ι] in
lemma purityChart_fibre {f : E → ι → ℝ} {I : Finset ι} {w c : E} {A : M}
    (hA : A ∈ purityChart f I w c) : negativeFibre A ∈ matrixFibre (lineRepresentative w A) :=
  negativeFibre_mem hA.2.1 hA.2.2.1 hA.2.2.2.1

end PurityChart
end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Support_MixedHomotopy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
open Set
section MixedHomotopy
variable {ν ι : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν] [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ ν
local notation "M" => Matrix ν ν ℝ

omit [DecidableEq ν] [Nonempty ν] [DecidableEq ι] in
lemma Admissible.cone_unit_positive {f : E → ι → ℝ} (_hf : Admissible f)
    {I : Finset ι} {u : E} (hu : ‖u‖ = 1) (hc : u ∈ commonPositiveCone f I) :
    ∀ i ∈ I, 0 < f u i := by
  intro i hi
  simpa only [homogeneousLift_unit f hu] using hc i hi

omit [DecidableEq ν] [Nonempty ν] [DecidableEq ι] in
lemma Admissible.maximal_cone_zero {f : E → ι → ℝ} (hf : Admissible f) {I : Finset ι}
    (hmax : ∀ u : E, ‖u‖ = 1 → I ⊆ positiveSupport f u → positiveSupport f u = I)
    {u : E} (hu : ‖u‖ = 1) (hc : u ∈ commonPositiveCone f I) :
    ∀ i ∉ I, f u i = 0 := by
  have he : positiveSupport f u = I := hmax u hu (fun i hi =>
    (mem_positiveSupport f u i).mpr (hf.cone_unit_positive hu hc i hi))
  intro i hi
  apply le_antisymm _ (hf.nonneg u hu i)
  by_contra hp
  have hh := (mem_positiveSupport f u i).mpr (lt_of_not_ge hp)
  rw [he] at hh
  exact hi hh

omit [Nonempty ν] in
lemma traceSphere_weights {A : M} (hA : A ∈ traceSphere ν) :
    Matrix.trace A⁺ + Matrix.trace A⁻ = 1 := by
  rw [← Matrix.trace_add,CFC.posPart_add_negPart A hA.1]; exact hA.2

end MixedHomotopy
end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Support_MixedHits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
open Set
section MixedHits
variable {ν ι : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν] [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ ν
local notation "M" => Matrix ν ν ℝ
local notation "Y" => EuclideanSpace ℝ ι
local notation "op" => Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)

omit [DecidableEq ι] in
lemma Admissible.negative_trace_pos {f : E → ι → ℝ} (hf : Admissible f) {A : M} {i : ι}
    (hi : signedExtension f A i < 0) : 0 < Matrix.trace A⁻ := by
  have hp := (hf.signedExtension_neg_iff A i).mp hi
  have hle : positiveExtension f A⁻ i ≤ Matrix.trace A⁻ := by
    rw [← hf.positiveExtension_sum (CFC.negPart_nonneg A)]
    exact Finset.single_le_sum (fun j _ => hf.positiveExtension_nonneg A⁻ j) (Finset.mem_univ i)
  exact hp.trans_le hle

lemma Admissible.original_ray_level_oai {f : E → ι → ℝ} (hf : Admissible f) {I : Finset ι}
    (hI : I.Nonempty) [Nonempty ↥(Iᶜ : Finset ι)]
    (hmax : ∀ u : E, ‖u‖ = 1 → I ⊆ positiveSupport f u → positiveSupport f u = I)
    {w : E} (hw : ‖w‖ = 1) (hwi : ∀ i ∈ I, 0 < f w i)
    {r : ι → ℝ} (hr : ∀ i ∈ I, 0 < r i) (hro : ∀ i ∉ I, r i = 0) (hrs : ∑ i, r i = 1)
    {z : EuclideanSpace ℝ ↥(Iᶜ : Finset ι)} (hz : ∀ i, 0 < z i) (hzs : ∑ i, z i = 1)
    {A : M} (hA : A ∈ traceSphere ν) {d : ℝ} (hd : 0 < d)
    (he : WithLp.toLp 2 (signedExtension f A) = d • blockVector I (1/2:ℝ) r (1/2:ℝ) z) :
    IsUnit A ∧ HasPositiveLine A ∧ op A⁺ w ≠ 0 ∧ 0 < Matrix.trace A⁻ ∧
      lineRepresentative w A ∈ orientedLevel f w r := by
  have hpos (i : ι) (hi : i ∈ I) : 0 < signedExtension f A i := by
    have hh := congrArg (fun v : Y => v i) he
    change signedExtension f A i = d * blockVector I (1/2:ℝ) r (1/2:ℝ) z i at hh
    rw [hh,blockVector_in _ _ _ _ _ hi]
    exact mul_pos hd (mul_pos (by norm_num) (hr i hi))
  have hneg (i : ↥(Iᶜ : Finset ι)) : signedExtension f A i.val < 0 := by
    have hh := congrArg (fun v : Y => v i.val) he
    change signedExtension f A i.val = d * blockVector I (1/2:ℝ) r (1/2:ℝ) z i.val at hh
    rw [hh,blockVector_out]
    exact mul_neg_of_pos_of_neg hd (mul_neg_of_neg_of_pos (by norm_num) (hz i))
  have hunit : IsUnit A := hf.signedExtension_fullSupport hA.1 (fun i => by
    by_cases hi : i ∈ I
    · exact ne_of_gt (hpos i hi)
    · exact ne_of_lt (hneg ⟨i,Finset.mem_compl.mpr hi⟩))
  obtain ⟨i,hi⟩ := hI
  have hline : HasPositiveLine A := hf.signedExtension_positive_rankOne hw hwi
    (fun j hj => (hneg ⟨j,Finset.mem_compl.mpr hj⟩).le) ⟨i,hpos i hi⟩
  have hAw : op A⁺ w ≠ 0 := by
    obtain ⟨u,hu,lam,hl,hP⟩ := hline
    have hui : 0 < f u i := (hf.signedExtension_line_labels hu hl hP i).mp (hpos i hi)
    have hwu : ⟪w,u⟫ ≠ 0 := fun heq => hf.orthogonal w u hw hu heq i ⟨hwi i hi,hui⟩
    exact unit_rankOne_inner_nonzero ⟨u,hu,lam,hl,hP⟩ hu hl hP hwu
  have hu := lineRepresentative_norm hAw
  have hc : lineRepresentative w A ∈ commonPositiveCone f I := by
    intro j hj
    rw [homogeneousLift_unit f hu]
    exact (hf.signedExtension_line_labels hu (hasPositiveLine_trace_pos hline)
      (positive_line_representative hline hAw) j).mp (hpos j hj)
  have hm := hf.negative_trace_pos (hneg (Classical.arbitrary ↥(Iᶜ : Finset ι)))
  have hchart : A ∈ purityChart f I w (lineRepresentative w A) :=
    ⟨hunit,hline,hAw,hm,hc,interior_safe_mem_own_chamber (hf.commonPositiveCone_interior_safe I hc)⟩
  have hg := hf.mixedHomotopy_zero hmax (fun _ => (0 : EuclideanSpace ℝ ↥(Iᶜ : Finset ι))) hA.1 hchart
  have hb : blockVector I (Matrix.trace A⁺) (f (lineRepresentative w A)) (Matrix.trace A⁻)
      (negativeCoordinates f I (negativeFibre A)) = d • blockVector I (1/2:ℝ) r (1/2:ℝ) z := by
    rw [← he,← hg]
    exact congrArg (blockVector I (Matrix.trace A⁺) (f (lineRepresentative w A)) (Matrix.trace A⁻))
      (fibreHomotopy_zero f I (lineRepresentative w A) (fun _ => 0) hu (negativeFibre A)).symm
  have hQ := purityChart_fibre hchart
  obtain ⟨-,-,-,ha,-⟩ := blockVector_ray (hasPositiveLine_trace_pos hline) hm (traceSphere_weights hA) hd
    (hf.maximal_cone_zero hmax hu hc) hro (hf.sum_one _ hu) hrs
    (hf.negativeCoordinates_sum (hf.commonPositiveCone_safe I hc) hQ) hzs hb
  exact ⟨hunit,hline,hAw,hm,hu,ha,(lineRepresentative_inner_pos hline hAw).le⟩

end MixedHits
end BorsukNine

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.BorsukNine.Admissible.original_ray_level_oai.{u_1, u_2} := @OAI.BorsukNine.Admissible.original_ray_level_oai.{u_1, u_2}
