-- Prove2me | solution 1 for OAI.BorsukNine.Admissible.chart_surgery_impossible
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T20:53:28.36369+00:00
-- url     : https://prove2.me/submissions/c949cd0e-428c-40d7-b87c-8d1b127e6c1d

import Mathlib
import Definitions.Def_OAIQ058B000
import Theorems.Thm_OAI_BorsukNine_Admissible_mixedHomotopy_hit
import Theorems.Thm_OAI_BorsukNine_Admissible_mixedHomotopy_zero
import Theorems.Thm_OAI_BorsukNine_Admissible_original_ray_level
import Theorems.Thm_OAI_BorsukNine_Admissible_traceHomotopy_ray

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

lemma blockVector_continuous {X : Type*} [TopologicalSpace X] (I : Finset ι)
    {lam mu : X → ℝ} {r : X → ι → ℝ} {z : X → EuclideanSpace ℝ ↥(Iᶜ : Finset ι)}
    (hl : Continuous lam) (hr : Continuous r) (hm : Continuous mu) (hz : Continuous z) :
    Continuous (fun x => blockVector I (lam x) (r x) (mu x) (z x)) := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  by_cases hi : i ∈ I
  · simp only [dite_eq_left hi]
    exact hl.mul ((continuous_apply i).comp hr)
  · simp only [dite_eq_right hi]
    let j : ↥(Iᶜ : Finset ι) := ⟨i,Finset.mem_compl.mpr hi⟩
    have hj : Continuous (fun x => z x j) := (PiLp.continuous_apply 2 _ j).comp hz
    exact hm.neg.mul hj

lemma blockVector_continuousOn {X : Type*} [TopologicalSpace X] (I : Finset ι) {S : Set X}
    {lam mu : X → ℝ} {r : X → ι → ℝ} {z : X → EuclideanSpace ℝ ↥(Iᶜ : Finset ι)}
    (hl : ContinuousOn lam S) (hr : ContinuousOn r S) (hm : ContinuousOn mu S) (hz : ContinuousOn z S) :
    ContinuousOn (fun x => blockVector I (lam x) (r x) (mu x) (z x)) S := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  exact blockVector_continuous I (continuousOn_iff_continuous_domRestrict.mp hl)
    (continuousOn_iff_continuous_domRestrict.mp hr) (continuousOn_iff_continuous_domRestrict.mp hm)
    (continuousOn_iff_continuous_domRestrict.mp hz)

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

lemma matrixConjugate_nonneg (e : E ≃ₗᵢ[ℝ] E) {A : M} (hA : 0 ≤ A) :
    0 ≤ matrixConjugate e A := map_nonneg _ hA

lemma matrixConjugate_rankOne (e : E ≃ₗᵢ[ℝ] E) (u : E) :
    matrixConjugate e (rankOne u) = rankOne (e u) := by
  apply (Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)).injective
  change op (matrixConjugate e (rankOne u)) = op (rankOne (e u))
  apply ContinuousLinearMap.ext
  intro v
  rw [matrixConjugate_action,rankOne_action,rankOne_action,map_smul]
  congr 1
  simpa using (e.inner_map_map u (e.symm v)).symm

lemma matrix_operator_trace (A : M) : LinearMap.trace ℝ E (op A).toLinearMap = Matrix.trace A := by
  rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin,Matrix.toEuclideanLin_eq_toLin_orthonormal]
  exact Matrix.trace_toLin_eq A _

lemma matrixConjugate_trace (e : E ≃ₗᵢ[ℝ] E) (A : M) :
    Matrix.trace (matrixConjugate e A) = Matrix.trace A := by
  rw [← matrix_operator_trace,← matrix_operator_trace]
  have he : (op (matrixConjugate e A)).toLinearMap = e.toLinearEquiv.conj (op A).toLinearMap := by
    apply LinearMap.ext
    intro v
    exact matrixConjugate_action e A v
  rw [he,LinearMap.trace_conj']

lemma matrixConjugate_kernel (e : E ≃ₗᵢ[ℝ] E) {A : M} {v : E} (hv : op A v = 0) :
    op (matrixConjugate e A) (e v) = 0 := by
  rw [matrixConjugate_action,e.symm_apply_apply,hv,map_zero]

lemma matrixConjugate_selfAdjoint (e : E ≃ₗᵢ[ℝ] E) {A : M} (hA : IsSelfAdjoint A) :
    IsSelfAdjoint (matrixConjugate e A) := by
  rw [IsSelfAdjoint,← map_star,hA.star_eq]

end MatrixTransport
end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_MatrixGeometry_ReflectionTransport
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace
section ReflectionTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma householder_apply (c x v : E) :
    householder c x v = (2 * (⟪c+x,v⟫ / ‖c+x‖ ^ 2)) • (c+x) - v := by
  rw [householder,Submodule.reflection_singleton_apply]
  simp only [RCLike.ofReal_real_eq_id, id_eq, two_smul, two_mul, add_smul]

lemma householder_send {c x : E} (h : ‖c‖ = ‖x‖) : householder c x c = x := by
  have hh := Submodule.reflection_sub (v := c) (w := -x) (by simpa using h)
  rw [sub_neg_eq_add,Submodule.reflection_orthogonal_apply] at hh
  exact neg_injective hh

lemma householder_at_self {c v : E} (hv : ⟪c,v⟫ = 0) :
    householder c c v = -v := by
  rw [householder_apply]
  simp [inner_add_left,hv]

end ReflectionTransport
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
local notation "M" => Matrix ν ν ℝ
local notation "op" => Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)

omit [Fintype ν] [DecidableEq ν] in
lemma rankOne_continuous : Continuous (rankOne (ν := ν)) := by
  apply continuous_matrix
  intro i j
  exact (PiLp.continuous_apply 2 (fun _ : ν => ℝ) i).mul
    (PiLp.continuous_apply 2 (fun _ : ν => ℝ) j)

lemma reflectionMatrix_action (c u v : E) :
    op (reflectionMatrix c u) v = householder c u v := by
  rw [reflectionMatrix,map_sub,map_smul,map_one,sub_apply,
    smul_apply,one_apply_eq_self,rankOne_action,householder_apply,
    smul_smul]
  congr 2
  ring

omit [DecidableEq ν] in
lemma householder_involutive (c u : E) : Function.Involutive (householder c u) :=
  (Submodule.span ℝ {c+u}).reflection_involutive

lemma reflectionMatrix_conjugate (c u : E) (B : M) :
    matrixConjugate (householder c u) B = reflectionMatrix c u * B * reflectionMatrix c u := by
  apply (Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)).injective
  change op (matrixConjugate (householder c u) B) = op (reflectionMatrix c u * B * reflectionMatrix c u)
  rw [map_mul,map_mul]
  apply ContinuousLinearMap.ext
  intro v
  rw [matrixConjugate_action]
  change _ = op (reflectionMatrix c u) (op B (op (reflectionMatrix c u) v))
  rw [reflectionMatrix_action,reflectionMatrix_action]
  congr 2

lemma reflectionMatrix_continuousOn (c : E) :
    ContinuousOn (reflectionMatrix c) {u | c+u ≠ 0} := by
  have hn : Continuous (fun u : E => ‖c+u‖^2) := (continuous_const.add continuous_id).norm.pow 2
  have hd : ContinuousOn (fun u : E => 2 / ‖c+u‖^2) {u | c+u ≠ 0} :=
    continuous_const.continuousOn.div hn.continuousOn
      (fun u hu => pow_ne_zero 2 (norm_ne_zero_iff.mpr hu))
  exact (hd.smul (rankOne_continuous.comp (continuous_const.add continuous_id)).continuousOn).sub
    continuous_const.continuousOn

lemma householder_matrix_joint_continuousOn (c : E) :
    ContinuousOn (fun p : E × M => matrixConjugate (householder c p.1) p.2)
      {p | c+p.1 ≠ 0} := by
  simp_rw [reflectionMatrix_conjugate]
  have hR : ContinuousOn (fun p : E × M => reflectionMatrix c p.1) {p | c+p.1 ≠ 0} :=
    (reflectionMatrix_continuousOn c).comp continuous_fst.continuousOn (fun _ h => h)
  exact (hR.mul continuous_snd.continuousOn).mul hR

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
local notation "op" => Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)

omit [DecidableEq ν] in
lemma householder_swap {c u : E} (h : ‖c‖ = ‖u‖) : householder c u u = c := by
  calc
    householder c u u = householder c u (householder c u c) := congrArg (householder c u) (householder_send h).symm
    _ = c := householder_involutive c u c

lemma matrixConjugate_householder_self {c : E} {Q : M} (hQ : IsSelfAdjoint Q)
    (hc : op Q c = 0) : matrixConjugate (householder c c) Q = Q := by
  apply (Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)).injective
  change op (matrixConjugate (householder c c) Q) = op Q
  apply ContinuousLinearMap.ext
  intro v
  rw [matrixConjugate_action]
  have hs : (householder c c).symm v = householder c c v := by
    apply (householder c c).injective
    rw [LinearIsometryEquiv.apply_symm_apply]
    exact (householder_involutive c c v).symm
  have hcz : op Q (c+c) = 0 := by rw [map_add,hc,add_zero]
  have hact : op Q (householder c c v) = -(op Q v) := by
    rw [householder_apply,map_sub,map_smul,hcz,smul_zero,zero_sub]
  rw [hs,hact,map_neg]
  have ho : ⟪c,op Q v⟫ = 0 := by
    rw [← ContinuousLinearMap.adjoint_inner_left,← ContinuousLinearMap.star_eq_adjoint,
      ← map_star,hQ.star_eq,hc,inner_zero_left]
  rw [householder_at_self ho,neg_neg]

lemma fibreTransport_nonneg (c u v : E) {Q : M} (hQ : 0 ≤ Q) :
    0 ≤ fibreTransport c u v Q :=
  matrixConjugate_nonneg _ (matrixConjugate_nonneg _ hQ)

lemma fibreTransport_trace (c u v : E) (Q : M) :
    Matrix.trace (fibreTransport c u v Q) = Matrix.trace Q := by
  simp only [fibreTransport,matrixConjugate_trace]

lemma fibreTransport_kernel {c u v : E} {Q : M} (hu : ‖c‖ = ‖u‖) (hv : ‖c‖ = ‖v‖)
    (hQ : op Q u = 0) : op (fibreTransport c u v Q) v = 0 := by
  have hQc : op (matrixConjugate (householder c u) Q) c = 0 := by
    simpa only [householder_swap hu] using matrixConjugate_kernel (householder c u) hQ
  simpa only [fibreTransport,householder_send hv] using matrixConjugate_kernel (householder c v) hQc

lemma fibreTransport_center {c u : E} {Q : M} (hQ : IsSelfAdjoint Q) (hu : ‖c‖ = ‖u‖)
    (hz : op Q u = 0) : fibreTransport c u c Q = matrixConjugate (householder c u) Q := by
  apply matrixConjugate_householder_self (matrixConjugate_selfAdjoint _ hQ)
  simpa only [householder_swap hu] using matrixConjugate_kernel (householder c u) hz

lemma fibreTransport_unit_iff {c u v : E} {Q : M} (hu : ‖c‖ = ‖u‖) (hv : ‖c‖ = ‖v‖) :
    IsUnit (rankOne v + fibreTransport c u v Q) ↔ IsUnit (rankOne u + Q) := by
  have he : rankOne v + fibreTransport c u v Q =
      matrixConjugate (householder c v) (matrixConjugate (householder c u) (rankOne u + Q)) := by
    rw [map_add,map_add,matrixConjugate_rankOne,householder_swap hu,
      matrixConjugate_rankOne,householder_send hv]; rfl
  rw [he]
  exact (isUnit_map_iff (matrixConjugate (householder c v)) _).trans
    (isUnit_map_iff (matrixConjugate (householder c u)) _)

lemma fibreTransport_continuousOn (c : E) :
    ContinuousOn (fun p : E × E × M => fibreTransport c p.1 p.2.1 p.2.2)
      {p | c+p.1 ≠ 0 ∧ c+p.2.1 ≠ 0} := by
  have hR₁ : ContinuousOn (fun p : E × E × M => reflectionMatrix c p.1)
      {p | c+p.1 ≠ 0 ∧ c+p.2.1 ≠ 0} :=
    (reflectionMatrix_continuousOn c).comp continuous_fst.continuousOn (fun _ h => h.1)
  have hR₂ : ContinuousOn (fun p : E × E × M => reflectionMatrix c p.2.1)
      {p | c+p.1 ≠ 0 ∧ c+p.2.1 ≠ 0} :=
    (reflectionMatrix_continuousOn c).comp continuous_snd.fst.continuousOn (fun _ h => h.2)
  simp only [fibreTransport,reflectionMatrix_conjugate]
  exact (hR₂.mul ((hR₁.mul continuous_snd.snd.continuousOn).mul hR₁)).mul hR₂

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

lemma signChamber_subset_safeNormals (Z : Set E) (c : E) :
    signChamber Z c ⊆ safeNormals Z := by
  intro x hx z hz h
  simpa [h] using hx z hz

lemma signChamber_convex (Z : Set E) (c : E) : Convex ℝ (signChamber Z c) := by
  intro x hx y hy a b ha hb hab z hz
  simp only [inner_add_left,real_inner_smul_left,mul_add]
  have h1 := hx z hz
  have h2 := hy z hz
  have hn1 := mul_nonneg ha h1.le
  have hn2 := mul_nonneg hb h2.le
  have he : ⟪c,z⟫ * (a * ⟪x,z⟫) + ⟪c,z⟫ * (b * ⟪y,z⟫) =
      a * (⟪c,z⟫ * ⟪x,z⟫) + b * (⟪c,z⟫ * ⟪y,z⟫) := by ring
  rw [he]
  rcases lt_or_eq_of_le ha with ha' | ha'
  · exact add_pos_of_pos_of_nonneg (mul_pos ha' h1) hn2
  · have hb' : b = 1 := by linarith
    simp [← ha',hb',h2]

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

lemma signChamber_smul {Z : Set E} {c u : E} (hu : u ∈ signChamber Z c)
    {t : ℝ} (ht : 0 < t) : t • u ∈ signChamber Z c := by
  intro z hz
  rw [real_inner_smul_left,mul_left_comm]
  exact mul_pos ht (hu z hz)

lemma chamber_interpolation_mem {Z : Set E} {c u : E} (hc : c ∈ safeNormals Z)
    (hu : u ∈ signChamber Z c) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    (1-t) • u + t • c ∈ signChamber Z c :=
  signChamber_convex Z c hu (mem_signChamber_self hc) (sub_nonneg.mpr ht.2) ht.1 (by ring)

lemma chamber_interpolation_ne_zero {Z : Set E} {c u : E} (hcZ : c ∈ Z)
    (hc : c ∈ safeNormals Z) (hu : u ∈ signChamber Z c)
    {t : ℝ} (ht : t ∈ Set.Icc 0 1) : (1-t) • u + t • c ≠ 0 := by
  intro he
  have h := chamber_interpolation_mem hc hu ht c hcZ
  simp [he] at h

lemma chamberPath_norm {Z : Set E} {c u : E} (hcZ : c ∈ Z)
    (hc : c ∈ safeNormals Z) (hu : u ∈ signChamber Z c)
    {t : ℝ} (ht : t ∈ Set.Icc 0 1) : ‖chamberPath c u t‖ = 1 := by
  have hn := chamber_interpolation_ne_zero hcZ hc hu ht
  simp only [chamberPath,norm_smul,norm_inv,norm_norm,inv_mul_cancel₀ (norm_ne_zero_iff.mpr hn)]

lemma chamberPath_mem {Z : Set E} {c u : E} (hcZ : c ∈ Z)
    (hc : c ∈ safeNormals Z) (hu : u ∈ signChamber Z c)
    {t : ℝ} (ht : t ∈ Set.Icc 0 1) : chamberPath c u t ∈ signChamber Z c :=
  signChamber_smul (chamber_interpolation_mem hc hu ht)
    (inv_pos.mpr (norm_pos_iff.mpr (chamber_interpolation_ne_zero hcZ hc hu ht)))

lemma chamberPath_one (c u : E) (hc : ‖c‖ = 1) : chamberPath c u 1 = c := by
  simp [chamberPath,hc]

lemma chamber_add_ne_zero {Z : Set E} {c u : E} (hcZ : c ∈ Z)
    (hc : c ∈ safeNormals Z) (hu : u ∈ signChamber Z c) : c+u ≠ 0 := by
  intro he
  have h := hu c hcZ
  have hn := hc c hcZ
  have hei : ⟪c,c⟫ + ⟪u,c⟫ = 0 := by rw [← inner_add_left,he,inner_zero_left]
  have hei' : ⟪u,c⟫ = -⟪c,c⟫ := by linarith
  rw [hei'] at h
  nlinarith [sq_nonneg ⟪c,c⟫]

lemma chamberPath_continuousOn {Z : Set E} {c : E} (hcZ : c ∈ Z)
    (hc : c ∈ safeNormals Z) : ContinuousOn (fun p : ℝ × E => chamberPath c p.2 p.1)
      (Set.Icc (0:ℝ) 1 ×ˢ signChamber Z c) := by
  have hs : Continuous (fun p : ℝ × E => (1-p.1) • p.2 + p.1 • c) :=
    ((continuous_const.sub continuous_fst).smul continuous_snd).add
      (continuous_fst.smul continuous_const)
  exact (hs.norm.continuousOn.inv₀ (fun p hp => norm_ne_zero_iff.mpr
    (chamber_interpolation_ne_zero hcZ hc hp.2 hp.1))).smul hs.continuousOn

end ChamberPath
end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_MatrixGeometry_PositiveSlice
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator
section PositiveSlice
variable {ν : Type*} [Fintype ν] [DecidableEq ν]
local notation "M" => Matrix ν ν ℝ

omit [DecidableEq ν] in
lemma flatGram_nonneg (x : EuclideanSpace ℝ (ν × ν)) : 0 ≤ flatGram x :=
  (Matrix.posSemidef_self_mul_conjTranspose _).nonneg

omit [DecidableEq ν] in
lemma flatGram_trace (x : EuclideanSpace ℝ (ν × ν)) : Matrix.trace (flatGram x) = ‖x‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [flatGram,Matrix.trace,Matrix.diag,Matrix.mul_apply,Matrix.conjTranspose_apply,
    star_trivial,Fintype.sum_prod_type]
  simp only [pow_two]
  rfl

omit [DecidableEq ν] in
lemma flatGram_continuous : Continuous (flatGram (ν := ν)) := by
  have h := (unflattenMatrix (ν := ν)).continuous_of_finiteDimensional
  exact h.mul h.star

lemma positive_slice_image : {Q : M | 0 ≤ Q ∧ Matrix.trace Q = 1} =
    flatGram '' Metric.sphere (0 : EuclideanSpace ℝ (ν × ν)) 1 := by
  ext Q
  constructor
  · rintro ⟨hQ,htr⟩
    let x : EuclideanSpace ℝ (ν × ν) := WithLp.toLp 2 (fun p => CFC.sqrt Q p.1 p.2)
    have hxQ : flatGram x = Q := by
      change CFC.sqrt Q * star (CFC.sqrt Q) = Q
      rw [(CFC.sqrt_nonneg Q).isSelfAdjoint.star_eq]
      exact CFC.sqrt_mul_sqrt_self Q
    have hn : ‖x‖ ^ 2 = 1 := by rw [← flatGram_trace,hxQ,htr]
    have hnorm : ‖x‖ = 1 := by nlinarith [norm_nonneg x]
    exact ⟨x,by simpa [dist_zero_right] using hnorm,hxQ⟩
  · rintro ⟨x,hx,rfl⟩
    refine ⟨flatGram_nonneg x,?_⟩
    have hnorm : ‖x‖ = 1 := by simpa [dist_zero_right] using hx
    rw [flatGram_trace,hnorm,one_pow]

lemma positive_slice_compact : IsCompact {Q : M | 0 ≤ Q ∧ Matrix.trace Q = 1} := by
  rw [positive_slice_image]
  exact (isCompact_sphere (0 : EuclideanSpace ℝ (ν × ν)) 1).image flatGram_continuous

end PositiveSlice
end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_MatrixGeometry_MatrixFibre
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator
section MatrixFibre
variable {ν : Type*} [Fintype ν] [DecidableEq ν]
local notation "E" => EuclideanSpace ℝ ν
local notation "M" => Matrix ν ν ℝ
local notation "op" => Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)

lemma psd_inner_nonneg {Q : M} (hQ : 0 ≤ Q) (v : E) : 0 ≤ ⟪v,op Q v⟫ := by
  have h := (Matrix.nonneg_iff_posSemidef.mp hQ).re_dotProduct_nonneg v.ofLp
  simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial]
  change 0 ≤ ∑ i, (Q *ᵥ v.ofLp) i * v i
  simpa only [RCLike.re_to_real,dotProduct,Pi.star_apply,star_trivial,mul_comm] using h

lemma nonunit_has_kernel (A : M) (hA : ¬ IsUnit A) :
    ∃ v : E, v ≠ 0 ∧ op A v = 0 := by
  have hdet : A.det = 0 := by
    by_contra h
    exact hA ((Matrix.isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr h))
  obtain ⟨v,hv,hAv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  refine ⟨WithLp.toLp 2 v,fun h => hv (WithLp.toLp_injective 2 h),?_⟩
  rw [Matrix.toEuclideanCLM_toLp,hAv,WithLp.toLp_zero]

lemma fibre_boundary_kernel {Q : M} (hQ : 0 ≤ Q) (u : E)
    (hnot : ¬ IsUnit (rankOne u + Q)) :
    ∃ v : E, ‖v‖ = 1 ∧ ⟪u,v⟫ = 0 ∧ op Q v = 0 := by
  obtain ⟨v,hv,hAv⟩ := nonunit_has_kernel _ hnot
  have hsum : ⟪v,op (rankOne u + Q) v⟫ = 0 := by rw [hAv,inner_zero_right]
  rw [map_add,add_apply,inner_add_right,rankOne_action,
    inner_smul_right,real_inner_comm u v] at hsum
  have hi : ⟪u,v⟫ = 0 := by
    nlinarith [psd_inner_nonneg hQ v,sq_nonneg ⟪u,v⟫]
  have hQv : op Q v = 0 := by
    simpa only [map_add,add_apply,rankOne_action,hi,zero_smul,zero_add] using hAv
  refine ⟨‖v‖⁻¹ • v,by simp [norm_smul,norm_inv,hv],?_,?_⟩
  · simp only [inner_smul_right,hi,mul_zero]
  · rw [map_smul,hQv,smul_zero]

end MatrixFibre
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

omit [DecidableEq ν] in
lemma matrix_trace_nonneg {A : M} (hA : 0 ≤ A) : 0 ≤ Matrix.trace A :=
  (Matrix.nonneg_iff_posSemidef.mp hA).trace_nonneg

lemma positive_ball_image : {Q : M | 0 ≤ Q ∧ Matrix.trace Q ≤ 1} =
    flatGram '' Metric.closedBall (0 : EuclideanSpace ℝ (ν × ν)) 1 := by
  ext Q
  constructor
  · rintro ⟨hQ,htr⟩
    let x : EuclideanSpace ℝ (ν × ν) := WithLp.toLp 2 (fun p => CFC.sqrt Q p.1 p.2)
    have hxQ : flatGram x = Q := by
      change CFC.sqrt Q * star (CFC.sqrt Q) = Q
      rw [(CFC.sqrt_nonneg Q).isSelfAdjoint.star_eq]
      exact CFC.sqrt_mul_sqrt_self Q
    have hn : ‖x‖ ^ 2 ≤ 1 := by rw [← flatGram_trace,hxQ]; exact htr
    have hn' : ‖x‖ ≤ 1 := by nlinarith [norm_nonneg x]
    exact ⟨x,by simpa [dist_zero_right] using hn',hxQ⟩
  · rintro ⟨x,hx,rfl⟩
    refine ⟨flatGram_nonneg x,?_⟩
    have hn : ‖x‖ ≤ 1 := by simpa [dist_zero_right] using hx
    rw [flatGram_trace]
    nlinarith [norm_nonneg x]

lemma positive_ball_compact : IsCompact {Q : M | 0 ≤ Q ∧ Matrix.trace Q ≤ 1} := by
  rw [positive_ball_image]
  exact (isCompact_closedBall (0 : EuclideanSpace ℝ (ν × ν)) 1).image flatGram_continuous

lemma traceSphere_closed : IsClosed (traceSphere ν) :=
  (isClosed_eq continuous_star continuous_id).inter
    (isClosed_eq (matrix_trace_continuous.comp CFC.continuous_abs) continuous_const)

lemma traceSphere_compact : IsCompact (traceSphere ν) := by
  have hK : IsCompact ((fun p : M × M => p.1 - p.2) ''
      ({Q : M | 0 ≤ Q ∧ Matrix.trace Q ≤ 1} ×ˢ {Q : M | 0 ≤ Q ∧ Matrix.trace Q ≤ 1})) :=
    (positive_ball_compact.prod positive_ball_compact).image (continuous_fst.sub continuous_snd)
  apply hK.of_isClosed_subset traceSphere_closed
  intro A hA
  have htr : Matrix.trace A⁺ + Matrix.trace A⁻ = 1 := by
    rw [← Matrix.trace_add,CFC.posPart_add_negPart A hA.1]
    exact hA.2
  refine ⟨(A⁺,A⁻),⟨⟨CFC.posPart_nonneg A,?_⟩,⟨CFC.negPart_nonneg A,?_⟩⟩,
    CFC.posPart_sub_negPart A hA.1⟩
  · linarith [matrix_trace_nonneg (CFC.negPart_nonneg A)]
  · linarith [matrix_trace_nonneg (CFC.posPart_nonneg A)]

lemma traceSphere_ne_zero {A : M} (hA : A ∈ traceSphere ν) : A ≠ 0 := by
  intro h
  simpa [h] using hA.2

end TraceSphere
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

omit [Fintype ι] in
lemma commonPositiveCone_active {f : E → ι → ℝ} {I : Finset ι} (hI : I.Nonempty)
    {c : E} (hc : c ∈ commonPositiveCone f I) : c ∈ activeVectors f I := by
  obtain ⟨i,hi⟩ := hI
  exact ⟨i,hi,hc i hi⟩

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

lemma Admissible.fibre_boundary_missing {f : E → ι → ℝ} (hf : Admissible f)
    {I : Finset ι} {u : E} (hu : u ∈ safeNormals (activeVectors f I))
    {Q : M} (hQ : 0 ≤ Q) (hnot : ¬ IsUnit (rankOne u + Q)) :
    ∃ i ∈ Iᶜ, positiveExtension f Q i = 0 := by
  obtain ⟨v,hv,huv,hQv⟩ := fibre_boundary_kernel hQ u hnot
  obtain ⟨i,hi⟩ := hf.support_nonempty hv
  have hip := (mem_positiveSupport f v i).mp hi
  refine ⟨i,?_,hf.positiveExtension_kernel hQ hv hQv hip⟩
  exact Finset.mem_compl.mpr (fun h => (ne_of_gt hip) (hf.safe_orthogonal_zero hu hv huv h))

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

omit [DecidableEq ν] [Nonempty ν] [Fintype ι] [DecidableEq ι] in
lemma orientedLevel_cone {f : E → ι → ℝ} {I : Finset ι} {w : E} {r : ι → ℝ}
    (hr : ∀ i ∈ I, 0 < r i) {u : E} (hu : u ∈ orientedLevel f w r) :
    u ∈ commonPositiveCone f I := by
  intro i hi
  rw [homogeneousLift_unit f hu.1,hu.2.1]
  exact hr i hi

omit [Nonempty ν] [DecidableEq ι] in
lemma Admissible.levelFibre_compact {f : E → ι → ℝ} (hf : Admissible f)
    (w : E) (r : ι → ℝ) : IsCompact (levelFibre f w r) := by
  have hA : Continuous (fun p : E × M => op p.2) :=
    (op).toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional.comp continuous_snd
  have he : levelFibre f w r = (orientedLevel f w r ×ˢ {Q : M | 0 ≤ Q ∧ Matrix.trace Q = 1}) ∩
      {p | op p.2 p.1 = 0} := by ext p; simp only [levelFibre,Set.mem_ofPred_eq,Set.mem_inter_iff,Set.mem_prod,and_assoc]
  rw [he]
  exact ((hf.orientedLevel_compact w r).prod positive_slice_compact).inter_right
    (isClosed_eq (hA.clm_apply continuous_fst) continuous_const)

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

omit [Nonempty ν] in
lemma centeredFibre_mem {c u : E} (hc : ‖c‖ = 1) (hu : ‖u‖ = 1) {Q : M}
    (hQ : Q ∈ matrixFibre u) : centeredFibre c u Q ∈ matrixFibre c := by
  refine ⟨matrixConjugate_nonneg _ hQ.1,?_,?_⟩
  · rw [centeredFibre,matrixConjugate_trace,hQ.2.1]
  · simpa only [centeredFibre,householder_swap (hc.trans hu.symm)] using
      matrixConjugate_kernel (householder c u) hQ.2.2

omit [Nonempty ν] [DecidableEq ι] in
lemma transportedFibre_mem {f : E → ι → ℝ} (hf : Admissible f) {I : Finset ι}
    (hI : I.Nonempty) {c u : E} (hc : c ∈ commonPositiveCone f I) (hcn : ‖c‖ = 1)
    (hun : ‖u‖ = 1) (hu : u ∈ signChamber (activeVectors f I) c)
    {t : ℝ} (ht : t ∈ Icc 0 1) {Q : M} (hQ : Q ∈ matrixFibre u) :
    transportedFibre c t u Q ∈ matrixFibre (chamberPath c u t) := by
  have hcs := hf.commonPositiveCone_safe I hc
  have hvn := chamberPath_norm (commonPositiveCone_active hI hc) hcs hu ht
  refine ⟨fibreTransport_nonneg _ _ _ hQ.1,?_,?_⟩
  · rw [transportedFibre,fibreTransport_trace,hQ.2.1]
  · exact fibreTransport_kernel (hcn.trans hun.symm) (hcn.trans hvn.symm) hQ.2.2

omit [Nonempty ν] in
lemma fibreHomotopy_one (f : E → ι → ℝ) (I : Finset ι) {c u : E} (hc : ‖c‖ = 1)
    (hu : ‖u‖ = 1) (g : M → EuclideanSpace ℝ ↥(Iᶜ : Finset ι)) {Q : M}
    (hQ : Q ∈ matrixFibre u) : fibreHomotopy f I c g 1 u Q = g (centeredFibre c u Q) := by
  simp only [fibreHomotopy,one_smul,transportedFibre,chamberPath_one c u hc,
    fibreTransport_center hQ.1.isSelfAdjoint (hc.trans hu.symm) hQ.2.2]
  simp only [centeredFibre]
  abel

lemma Admissible.fibreHomotopy_boundary_misses {f : E → ι → ℝ} (hf : Admissible f)
    {I : Finset ι} (hI : I.Nonempty) {c u : E} (hc : c ∈ commonPositiveCone f I)
    (hcn : ‖c‖ = 1) (hun : ‖u‖ = 1) (hu : u ∈ signChamber (activeVectors f I) c)
    (g : M → EuclideanSpace ℝ ↥(Iᶜ : Finset ι)) {ε : ℝ} (hε : 0 < ε)
    (hg : ∀ Q ∈ matrixFibre c, ‖g Q - negativeCoordinates f I Q‖ < ε)
    (z : EuclideanSpace ℝ ↥(Iᶜ : Finset ι)) (hz : ∀ i, ε < z i)
    {t : ℝ} (ht : t ∈ Icc 0 1) {Q : M} (hQ : Q ∈ matrixFibre u)
    (hn : ¬ IsUnit (rankOne u + Q)) : fibreHomotopy f I c g t u Q ≠ z := by
  have hcs := hf.commonPositiveCone_safe I hc
  have hvmem := chamberPath_mem (commonPositiveCone_active hI hc) hcs hu ht
  have hvn := chamberPath_norm (commonPositiveCone_active hI hc) hcs hu ht
  have hT := transportedFibre_mem hf hI hc hcn hun hu ht hQ
  have htn : ¬ IsUnit (rankOne (chamberPath c u t) + transportedFibre c t u Q) := by
    intro h
    exact hn ((fibreTransport_unit_iff (hcn.trans hun.symm) (hcn.trans hvn.symm)).mp h)
  obtain ⟨i,hi,hzi⟩ := hf.fibre_boundary_missing (signChamber_subset_safeNormals _ _ hvmem) hT.1 htn
  let j : ↥(Iᶜ : Finset ι) := ⟨i,hi⟩
  have hC := centeredFibre_mem hcn hun hQ
  have hb : |(g (centeredFibre c u Q) - negativeCoordinates f I (centeredFibre c u Q)) j| < ε :=
    lt_of_le_of_lt (by simpa only [Real.norm_eq_abs] using
      (PiLp.norm_apply_le (g (centeredFibre c u Q) - negativeCoordinates f I (centeredFibre c u Q)) j)) (hg _ hC)
  intro he
  have hj := congrArg (fun v : EuclideanSpace ℝ ↥(Iᶜ : Finset ι) => v j) he
  change positiveExtension f (transportedFibre c t u Q) i +
    t * ((g (centeredFibre c u Q) - negativeCoordinates f I (centeredFibre c u Q)) j) = z j at hj
  rw [hzi,zero_add] at hj
  have hjb := hz j
  have hab := abs_lt.mp hb
  have hle := mul_le_mul_of_nonneg_left hab.2.le ht.1
  have hh : t * ε ≤ ε := by nlinarith [ht.2]
  linarith

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

omit [Nonempty ν] in
lemma centeredFibre_continuousOn (c : E) :
    ContinuousOn (fun p : E × M => centeredFibre c p.1 p.2) {p | c+p.1 ≠ 0} :=
  householder_matrix_joint_continuousOn c

omit [Nonempty ν] in
lemma fibreTransport_continuousOn_comp {X : Type*} [TopologicalSpace X]
    {S : Set X} (c : E) {u v : X → E} {Q : X → M}
    (hu : ContinuousOn u S) (hv : ContinuousOn v S) (hQ : ContinuousOn Q S)
    (hc : ∀ x ∈ S, c+u x ≠ 0 ∧ c+v x ≠ 0) :
    ContinuousOn (fun x => fibreTransport c (u x) (v x) (Q x)) S := by
  exact ContinuousOn.comp' (g := fun p : E × E × M => fibreTransport c p.1 p.2.1 p.2.2)
    (f := fun x : X => (u x,v x,Q x)) (s := S)
    (fibreTransport_continuousOn c) (hu.prodMk (hv.prodMk hQ)) hc

omit [DecidableEq ν] [Nonempty ν] in
lemma chamberPath_matrix_continuousOn {Z : Set E} {c : E} (hcz : c ∈ Z)
    (hcs : c ∈ safeNormals Z) :
    ContinuousOn (fun p : ℝ × E × M => chamberPath c p.2.1 p.1)
      {p | p.1 ∈ Icc 0 1 ∧ p.2.1 ∈ signChamber Z c} := by
  have hp : Continuous (fun p : ℝ × E × M => (p.1,p.2.1)) :=
    continuous_fst.prodMk continuous_snd.fst
  exact ContinuousOn.comp' (g := fun p : ℝ × E => chamberPath c p.2 p.1)
    (f := fun p : ℝ × E × M => (p.1,p.2.1))
    (chamberPath_continuousOn hcz hcs) hp.continuousOn (fun _ h => h)

omit [DecidableEq ι] in
omit [Nonempty ν] in
lemma transportedFibre_continuousOn {f : E → ι → ℝ} (hf : Admissible f) {I : Finset ι}
    (hI : I.Nonempty) {c : E} (hc : c ∈ commonPositiveCone f I) :
    ContinuousOn (fun p : ℝ × E × M => transportedFibre c p.1 p.2.1 p.2.2)
      {p | p.1 ∈ Icc 0 1 ∧ p.2.1 ∈ signChamber (activeVectors f I) c} := by
  have hcs := hf.commonPositiveCone_safe I hc
  have hcz := commonPositiveCone_active hI hc
  apply fibreTransport_continuousOn_comp c continuous_snd.fst.continuousOn
    (chamberPath_matrix_continuousOn hcz hcs) continuous_snd.snd.continuousOn
  intro p hp
  exact ⟨chamber_add_ne_zero hcz hcs hp.2,
    chamber_add_ne_zero hcz hcs (chamberPath_mem hcz hcs hp.2 hp.1)⟩

lemma Admissible.fibreHomotopy_continuousOn {f : E → ι → ℝ} (hf : Admissible f) {I : Finset ι}
    (hI : I.Nonempty) {c : E} (hc : c ∈ commonPositiveCone f I) (hcn : ‖c‖ = 1)
    (g : M → EuclideanSpace ℝ ↥(Iᶜ : Finset ι)) (hg : Continuous g) :
    ContinuousOn (fun p : ℝ × E × M => fibreHomotopy f I c g p.1 p.2.1 p.2.2)
      {p | p.1 ∈ Icc 0 1 ∧ ‖p.2.1‖ = 1 ∧
        p.2.1 ∈ signChamber (activeVectors f I) c ∧ p.2.2 ∈ matrixFibre p.2.1} := by
  have hcs := hf.commonPositiveCone_safe I hc
  have hcz := commonPositiveCone_active hI hc
  let S : Set (ℝ × E × M) := {p | p.1 ∈ Icc 0 1 ∧ ‖p.2.1‖ = 1 ∧
        p.2.1 ∈ signChamber (activeVectors f I) c ∧ p.2.2 ∈ matrixFibre p.2.1}
  have hT : ContinuousOn (fun p : ℝ × E × M => transportedFibre c p.1 p.2.1 p.2.2) S :=
    (transportedFibre_continuousOn hf hI hc).mono (fun _ hp => ⟨hp.1,hp.2.2.1⟩)
  have hC : ContinuousOn (fun p : ℝ × E × M => centeredFibre c p.2.1 p.2.2) S :=
    (centeredFibre_continuousOn c).comp continuous_snd.continuousOn
      (fun _ hp => chamber_add_ne_zero hcz hcs hp.2.2.1)
  have hET := (hf.negativeCoordinates_continuousOn I).comp hT
    (fun _ hp => (transportedFibre_mem hf hI hc hcn hp.2.1 hp.2.2.1 hp.1 hp.2.2.2).1)
  have hEC := (hf.negativeCoordinates_continuousOn I).comp hC
    (fun _ hp => (centeredFibre_mem hcn hp.2.1 hp.2.2.2).1)
  exact hET.add (continuous_fst.continuousOn.smul ((hg.comp_continuousOn hC).sub hEC))

end FibreContinuity
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

end RankOnePreimage
end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_MatrixGeometry_SpectralChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator Topology
section SpectralChart
variable {ν : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν]
local notation "E" => EuclideanSpace ℝ ν
local notation "M" => Matrix ν ν ℝ
local notation "op" => Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)

omit [Nonempty ν] in
lemma positiveProjection_action {A : M} (hA : IsSelfAdjoint A) (hU : IsUnit A)
    {v : E} (hv : v ∈ LinearMap.range (op A⁺).toLinearMap) :
    op (positiveProjection A) v = v := by
  obtain ⟨x,rfl⟩ := hv
  have hAP : A * A⁺ = A⁺ * A⁺ := by
    calc
      A * A⁺ = (A⁺ - A⁻) * A⁺ := by rw [CFC.posPart_sub_negPart A hA]
      _ = A⁺ * A⁺ := by rw [sub_mul,CFC.negPart_mul_posPart,sub_zero]
  have he : positiveProjection A * A⁺ = A⁺ := by
    dsimp [positiveProjection]
    rw [mul_assoc,← hAP,← mul_assoc,Ring.inverse_mul_cancel A hU,one_mul]
  have hh := congrArg (fun B : M => op B x) he
  simpa only [map_mul,mul_apply_eq_comp,ContinuousLinearMap.coe_coe] using hh

omit [Nonempty ν] in
lemma positiveProjection_kills {A : M} {u v : E} {lam : ℝ}
    (hP : A⁺ = lam • rankOne u) (hv : ⟪u,v⟫ = 0) :
    op (positiveProjection A) v = 0 := by
  simp only [positiveProjection,map_mul,mul_apply_eq_comp,hP,map_smul,
    smul_apply,rankOne_action,hv,zero_smul,map_zero,smul_zero]

omit [Nonempty ν] in
lemma positiveRange_separated_of_close {A B : M} (hB : IsSelfAdjoint B)
    (hBU : IsUnit B) {u : E} {lam : ℝ} (hP : A⁺ = lam • rankOne u)
    (hclose : ‖op (positiveProjection B) - op (positiveProjection A)‖ < 1)
    {v : E} (hv : v ∈ LinearMap.range (op B⁺).toLinearMap) (horth : ⟪u,v⟫ = 0) : v = 0 := by
  have he : (op (positiveProjection B) - op (positiveProjection A)) v = v := by
    rw [sub_apply,positiveProjection_action hB hBU hv,
      positiveProjection_kills hP horth,sub_zero]
  have hn := ContinuousLinearMap.le_opNorm (op (positiveProjection B) - op (positiveProjection A)) v
  rw [he] at hn
  apply norm_eq_zero.mp
  have hp := norm_nonneg v
  nlinarith

omit [Nonempty ν] in
lemma positive_eq_rankOne_of_separated {A : M} {w : E}
    (hAw : op A⁺ w ≠ 0)
    (hsep : ∀ v ∈ LinearMap.range (op A⁺).toLinearMap, ⟪w,v⟫ = 0 → v = 0) :
    ∃ u : E, ‖u‖ = 1 ∧ ∃ lam : ℝ, 0 < lam ∧ A⁺ = lam • rankOne u := by
  let v : E := op A⁺ w
  let u : E := ‖v‖⁻¹ • v
  have hu : ‖u‖ = 1 := by simp [u,norm_smul,norm_inv,hAw,v]
  have hur : u ∈ LinearMap.range (op A⁺).toLinearMap :=
    Submodule.smul_mem _ _ (LinearMap.mem_range_self _ w)
  have hwu : ⟪w,u⟫ ≠ 0 := by
    intro hz
    have hu0 := hsep u hur hz
    simp [hu0] at hu
  have hr := subspace_eq_span_of_inner_separates
    (LinearMap.range (op A⁺).toLinearMap) w u hur hwu hsep
  have he := symmetric_eq_rankOne_of_range (CFC.posPart_nonneg A).isSelfAdjoint hu hr.le
  have hl : 0 ≤ ⟪u,op A⁺ u⟫ := by
    rw [← sqrt_action_norm_sq A⁺ (CFC.posPart_nonneg A) u]
    positivity
  have hl0 : ⟪u,op A⁺ u⟫ ≠ 0 := by
    intro hz
    have hP0 : A⁺ = 0 := by simpa only [hz,zero_smul] using he
    apply hAw
    simp [hP0]
  exact ⟨u,hu,_,lt_of_le_of_ne hl (Ne.symm hl0),he⟩

omit [Nonempty ν] in
lemma positiveProjection_continuousAt {X : Type*} [TopologicalSpace X]
    (A : X → M) (hA : Continuous A) (hSA : ∀ x, IsSelfAdjoint (A x))
    {x : X} (hU : IsUnit (A x)) : ContinuousAt (positiveProjection ∘ A) x := by
  have hP : Continuous (fun x => (A x)⁺) :=
    (matrix_posPart_continuousOn.comp_continuous hA (fun y => hSA y))
  have hInv : ContinuousAt (fun y => Ring.inverse (A y)) x := by
    obtain ⟨a,ha⟩ := hU
    have hi := NormedRing.inverse_continuousAt a
    rw [ha] at hi
    exact hi.comp hA.continuousAt
  exact hInv.mul hP.continuousAt

omit [Nonempty ν] in
lemma positive_line_eventually {X : Type*} [TopologicalSpace X]
    (A : X → M) (hA : Continuous A) (hSA : ∀ x, IsSelfAdjoint (A x))
    {x : X} (hU : IsUnit (A x)) {w : E} (hw : ‖w‖ = 1)
    {lam : ℝ} (hlam : 0 < lam) (hP : (A x)⁺ = lam • rankOne w) :
    ∀ᶠ y in 𝓝 x, IsUnit (A y) ∧ ∃ u : E, ‖u‖ = 1 ∧
      ∃ t : ℝ, 0 < t ∧ (A y)⁺ = t • rankOne u := by
  have hop : Continuous (fun B : M => op B) :=
    (op).toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional
  have hQ := hop.continuousAt.comp (positiveProjection_continuousAt A hA hSA hU)
  have hclose : ∀ᶠ y in 𝓝 x, ‖op (positiveProjection (A y)) - op (positiveProjection (A x))‖ < 1 := by
    have ht := (hQ.sub (continuousAt_const (y := op (positiveProjection (A x))))).norm
    exact ht.eventually_lt continuousAt_const (by simp)
  have hPcont : Continuous (fun y => (A y)⁺) :=
    matrix_posPart_continuousOn.comp_continuous hA (fun y => hSA y)
  have hvcont : Continuous (fun y => op (A y)⁺ w) := (hop.comp hPcont).clm_apply continuous_const
  have hw0 : op (A x)⁺ w ≠ 0 := by
    rw [hP,map_smul,smul_apply,rankOne_action,real_inner_self_eq_norm_sq,hw]
    have hwne : w ≠ 0 := by intro he; simp only [he,norm_zero] at hw; norm_num at hw
    simpa only [one_pow,one_smul] using smul_ne_zero (ne_of_gt hlam) hwne
  have hv : ∀ᶠ y in 𝓝 x, op (A y)⁺ w ≠ 0 := hvcont.continuousAt.eventually_ne hw0
  have hunit : ∀ᶠ y in 𝓝 x, IsUnit (A y) :=
    hA.continuousAt.preimage_mem_nhds (Units.isOpen.mem_nhds hU)
  filter_upwards [hclose,hv,hunit] with y hy hyv hyU
  refine ⟨hyU,positive_eq_rankOne_of_separated hyv ?_⟩
  exact fun v hv he => positiveRange_separated_of_close (hSA y) hyU hP hy hv he

end SpectralChart
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
lemma lineRepresentative_continuousOn {X : Type*} [TopologicalSpace X]
    (A : X → M) (hA : Continuous A) (hSA : ∀ x, IsSelfAdjoint (A x)) (w : E) :
    ContinuousOn (fun x => lineRepresentative w (A x)) {x | op (A x)⁺ w ≠ 0} := by
  have hop : Continuous (fun B : M => op B) :=
    (op).toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional
  have hP : Continuous (fun x => (A x)⁺) :=
    matrix_posPart_continuousOn.comp_continuous hA hSA
  have hv : Continuous (fun x => op (A x)⁺ w) := (hop.comp hP).clm_apply continuous_const
  exact (hv.norm.continuousOn.inv₀ (fun _ hx => norm_ne_zero_iff.mpr hx)).smul hv.continuousOn

omit [Nonempty ν] in
lemma positive_line_isOpen {X : Type*} [TopologicalSpace X]
    (A : X → M) (hA : Continuous A) (hSA : ∀ x, IsSelfAdjoint (A x)) :
    IsOpen {x | IsUnit (A x) ∧ HasPositiveLine (A x)} := by
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  obtain ⟨u,hu,lam,hl,he⟩ := hx.2
  exact positive_line_eventually A hA hSA hx.1 hu hl he

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
-- module Solutions.OAIQ058_BK.Borsuk_Projectors_CompactLocalHomotopy
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open Set
open scoped Topology

lemma compact_local_homotopy {X E : Type*} [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] [TopologicalSpace E] [Zero E]
    {U C : Set X} (hU : IsOpen U) (hC : IsCompact C) (hCU : C ⊆ U)
    (H : X → E) (hH : Continuous H) (hHz : ∀ x, H x ≠ 0)
    (K : ℝ × X → E) (hK : ContinuousOn K (Icc (0:ℝ) 1 ×ˢ U))
    (hK0 : ∀ x ∈ U, K (0,x) = H x)
    (hKz : ∀ t ∈ Icc (0:ℝ) 1, ∀ x ∈ U, K (t,x) ≠ 0)
    (B : Set E) (houtside : ∀ x ∉ U, H x ∉ B)
    (hhits : ∀ t ∈ Icc (0:ℝ) 1, ∀ x ∈ U, K (t,x) ∈ B → x ∈ C)
    (hend : ∀ x ∈ U, K (1,x) ∉ B) :
    ∃ G : ℝ × X → E, ContinuousOn G (Icc (0:ℝ) 1 ×ˢ Set.univ) ∧
      (∀ x, G (0,x) = H x) ∧
      (∀ t ∈ Icc (0:ℝ) 1, ∀ x, G (t,x) ≠ 0) ∧
      (∀ x, G (1,x) ∉ B) := by
  classical
  obtain ⟨q,hq1,-,hqs,hqb⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen hC hU hCU
  let G : ℝ × X → E := fun p => if p.2 ∈ U then K (p.1 * q p.2,p.2) else H p.2
  have htm (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) (x : X) : t * q x ∈ Icc (0:ℝ) 1 :=
    ⟨mul_nonneg ht.1 (hqb x).1,
      (mul_le_mul_of_nonneg_right ht.2 (hqb x).1).trans (by simpa using (hqb x).2)⟩
  have hG : ContinuousOn G (Icc (0:ℝ) 1 ×ˢ Set.univ) := by
    intro p hp
    by_cases hx : p.2 ∈ U
    · have hc : ContinuousOn (fun p : ℝ × X => K (p.1 * q p.2,p.2))
          (Icc (0:ℝ) 1 ×ˢ U) := hK.comp
        ((continuous_fst.mul (q.continuous.comp continuous_snd)).prodMk continuous_snd).continuousOn
        (fun p hp => ⟨htm p.1 hp.1 p.2,hp.2⟩)
      have hnear : ∀ᶠ p' in 𝓝 p, p'.2 ∈ U :=
        continuous_snd.continuousAt.preimage_mem_nhds (hU.mem_nhds hx)
      have hset : Icc (0:ℝ) 1 ×ˢ U ∈ 𝓝[Icc (0:ℝ) 1 ×ˢ Set.univ] p := by
        filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds hnear,
          self_mem_nhdsWithin] with p' hu hi
        exact ⟨hi.1,hu⟩
      apply ((hc p ⟨hp.1,hx⟩).mono_of_mem_nhdsWithin hset).congr_of_eventuallyEq
      · filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds hnear] with p' hu
        simp [G,hu]
      · simp [G,hx]
    · have hxq : p.2 ∉ tsupport q := fun h => hx (hqs h)
      have hnear : ∀ᶠ p' in 𝓝 p, p'.2 ∉ tsupport q :=
        continuous_snd.continuousAt.preimage_mem_nhds ((isClosed_tsupport q).isOpen_compl.mem_nhds hxq)
      apply (hH.comp continuous_snd).continuousAt.continuousWithinAt.congr_of_eventuallyEq
      · filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds hnear] with p' hq
        have hz : q p'.2 = 0 := image_eq_zero_of_notMem_tsupport hq
        by_cases hu : p'.2 ∈ U
        · simp [G,hu,hz,hK0 p'.2 hu]
        · simp [G,hu]
      · simp [G,hx]
  refine ⟨G,hG,?_,?_,?_⟩
  · intro x
    by_cases hx : x ∈ U
    · simp [G,hx,hK0 x hx]
    · simp [G,hx]
  · intro t ht x
    by_cases hx : x ∈ U
    · simpa only [G,ite_eq_left hx] using hKz _ (htm t ht x) x hx
    · simpa only [G,ite_eq_right hx] using hHz x
  · intro x hb
    by_cases hx : x ∈ U
    · have hh : K (q x,x) ∈ B := by simpa only [G,ite_eq_left hx,one_mul] using hb
      have hc := hhits _ (hqb x) x hx hh
      rw [hq1 hc] at hh
      exact hend x hx hh
    · exact houtside x hx (by simpa only [G,ite_eq_right hx] using hb)

end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Projectors_FiniteOpenGlue
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped BigOperators Topology

lemma finiteOpenGlue_eq {κ X Y : Type*} [Fintype κ] [AddCommMonoid Y]
    {S : κ → Set X} (hS : Pairwise (fun i j => Disjoint (S i) (S j))) (f : κ → X → Y)
    {i : κ} {x : X} (hx : x ∈ S i) : finiteOpenGlue S f x = f i x := by
  classical
  rw [finiteOpenGlue,Finset.sum_eq_single i]
  · simp [hx]
  · intro j hj hji
    have hjx : x ∉ S j := fun hp => Set.disjoint_left.mp (hS hji) hp hx
    simp [hjx]
  · simp

lemma finiteOpenGlue_continuousOn_prod {κ X Y : Type*} [Fintype κ]
    [TopologicalSpace X] [TopologicalSpace Y] [AddCommMonoid Y]
    {S : κ → Set X} (hSo : ∀ i, IsOpen (S i)) (hS : Pairwise (fun i j => Disjoint (S i) (S j)))
    (f : κ → ℝ × X → Y) (hf : ∀ i, ContinuousOn (f i) (Set.Icc (0:ℝ) 1 ×ˢ S i)) :
    ContinuousOn (finiteOpenGlue (fun i => {p : ℝ × X | p.2 ∈ S i}) f)
      (Set.Icc (0:ℝ) 1 ×ˢ ⋃ i, S i) := by
  intro p hp
  obtain ⟨i,hpi⟩ := Set.mem_iUnion.mp hp.2
  have hn : ∀ᶠ q in 𝓝 p, q.2 ∈ S i :=
    continuous_snd.continuousAt.preimage_mem_nhds ((hSo i).mem_nhds hpi)
  have hs : Set.Icc (0:ℝ) 1 ×ˢ S i ∈ 𝓝[Set.Icc (0:ℝ) 1 ×ˢ ⋃ i, S i] p := by
    filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds hn,self_mem_nhdsWithin] with q hq hqi
    exact ⟨hqi.1,hq⟩
  have hSp : Pairwise (fun i j => Disjoint {p : ℝ × X | p.2 ∈ S i} {p : ℝ × X | p.2 ∈ S j}) := by
    intro i j hij
    exact Set.disjoint_left.mpr (fun p hi hj => Set.disjoint_left.mp (hS hij) hi hj)
  apply ((hf i p ⟨hp.1,hpi⟩).mono_of_mem_nhdsWithin hs).congr_of_eventuallyEq
  · filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds hn] with q hq
    exact finiteOpenGlue_eq hSp f hq
  · exact finiteOpenGlue_eq hSp f hpi

end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Projectors_CompactTargetHits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open Set
lemma compact_target_hits {P X Y : Type*} [TopologicalSpace P] [CompactSpace P]
    [TopologicalSpace X] [TopologicalSpace Y] [T1Space Y]
    (φ : P → X) (hφ : Continuous φ) (K : ℝ × P → Y)
    (hK : ContinuousOn K (Icc (0:ℝ) 1 ×ˢ univ)) (y : Y) :
    IsCompact {x : X | ∃ p : P, φ p = x ∧ ∃ t ∈ Icc (0:ℝ) 1, K (t,p) = y} := by
  have hC : IsCompact ((Icc (0:ℝ) 1 ×ˢ (univ : Set P)) ∩ K ⁻¹' {y}) :=
    ((isCompact_Icc.prod isCompact_univ) : IsCompact (Icc (0:ℝ) 1 ×ˢ (univ : Set P))).of_isClosed_subset
      (hK.preimage_isClosed_of_isClosed (isClosed_Icc.prod isClosed_univ) isClosed_singleton) inter_subset_left
  have he : {x : X | ∃ p : P, φ p = x ∧ ∃ t ∈ Icc (0:ℝ) 1, K (t,p) = y} =
      (fun q : ℝ × P => φ q.2) '' ((Icc (0:ℝ) 1 ×ˢ (univ : Set P)) ∩ K ⁻¹' {y}) := by
    ext x
    constructor
    · rintro ⟨p,hp,t,ht,hk⟩
      exact ⟨(t,p),⟨⟨ht,mem_univ _⟩,hk⟩,hp⟩
    · rintro ⟨⟨t,p⟩,⟨⟨ht,-⟩,hk⟩,hp⟩
      exact ⟨p,hp,t,ht,hk⟩
  rw [he]
  exact hC.image (hφ.comp continuous_snd)
end BorsukNine

namespace BorsukNine
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
open Set
section LevelModel
variable {ν ι κ : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν] [Fintype ι] [DecidableEq ι] [Fintype κ]
local notation "E" => EuclideanSpace ℝ ν
local notation "M" => Matrix ν ν ℝ

omit [Fintype ι] [DecidableEq ι] in
omit [Nonempty ν] in
lemma balancedModel_continuous (f : E → ι → ℝ) (w : E) (r : ι → ℝ) :
    Continuous (balancedModel (f := f) (w := w) (r := r)) := by
  apply Continuous.subtype_mk
  change Continuous (fun p : levelFibre f w r => (1/2:ℝ) • rankOne p.val.1 - (1/2:ℝ) • p.val.2)
  exact ((continuous_const : Continuous (fun _ : levelFibre f w r => (1/2:ℝ))).smul
    (rankOne_continuous.comp continuous_subtype_val.fst)).sub
    ((continuous_const : Continuous (fun _ : levelFibre f w r => (1/2:ℝ))).smul continuous_subtype_val.snd)

omit [Nonempty ν] [Fintype ι] [DecidableEq ι] [Fintype κ] in
lemma modelChambers_open (f : E → ι → ℝ) (I : Finset ι) (w : E) (r : ι → ℝ) (c : κ → E) (j : κ) :
    IsOpen (modelChambers f I w r c j) :=
  isOpen_interior.preimage continuous_subtype_val.fst

omit [Nonempty ν] [Fintype ι] [DecidableEq ι] [Fintype κ] in
lemma modelChambers_disjoint {f : E → ι → ℝ} {I : Finset ι} {w : E} {r : ι → ℝ} {c : κ → E}
    (hd : Pairwise (fun i j => Disjoint (interior (signChamber (activeVectors f I) (c i)))
      (interior (signChamber (activeVectors f I) (c j))))) :
    Pairwise (fun i j => Disjoint (modelChambers f I w r c i) (modelChambers f I w r c j)) := by
  intro i j hij
  exact Set.disjoint_left.mpr (fun p hp hq => Set.disjoint_left.mp (hd hij) hp hq)

omit [Nonempty ν] [Fintype ι] [DecidableEq ι] [Fintype κ] in
lemma modelChambers_cover {f : E → ι → ℝ} {I : Finset ι} {w : E} {r : ι → ℝ} {c : κ → E}
    (hc : orientedLevel f w r ⊆ ⋃ j, interior (signChamber (activeVectors f I) (c j))) :
    (⋃ j, modelChambers f I w r c j) = univ := by
  apply eq_univ_of_forall
  intro p
  obtain ⟨j,hj⟩ := mem_iUnion.mp (hc p.property.1)
  exact mem_iUnion.mpr ⟨j,hj⟩

omit [Nonempty ν] in
lemma levelHomotopy_eq {f : E → ι → ℝ} {I : Finset ι} {w : E} {r : ι → ℝ} {c : κ → E}
    (hd : Pairwise (fun i j => Disjoint (interior (signChamber (activeVectors f I) (c i)))
      (interior (signChamber (activeVectors f I) (c j)))))
    (g : κ → M → EuclideanSpace ℝ ↥(Iᶜ : Finset ι)) {p : levelFibre f w r} {j : κ}
    (hp : p.val.1 ∈ interior (signChamber (activeVectors f I) (c j))) (t : ℝ) :
    levelHomotopy f I w r c g (t,p) = fibreHomotopy f I (c j) (g j) t p.val.1 p.val.2 := by
  apply finiteOpenGlue_eq
  · intro a b hab
    exact Set.disjoint_left.mpr (fun q ha hb => Set.disjoint_left.mp (hd hab) ha hb)
  · exact hp

lemma Admissible.levelHomotopy_continuousOn {f : E → ι → ℝ} (hf : Admissible f)
    {I : Finset ι} (hI : I.Nonempty) {w : E} {r : ι → ℝ} (c : κ → E)
    (hc : ∀ j, c j ∈ commonPositiveCone f I) (hcn : ∀ j, ‖c j‖ = 1)
    (hd : Pairwise (fun i j => Disjoint (interior (signChamber (activeVectors f I) (c i)))
      (interior (signChamber (activeVectors f I) (c j)))))
    (hcover : orientedLevel f w r ⊆ ⋃ j, interior (signChamber (activeVectors f I) (c j)))
    (g : κ → M → EuclideanSpace ℝ ↥(Iᶜ : Finset ι)) (hg : ∀ j, Continuous (g j)) :
    ContinuousOn (levelHomotopy f I w r c g) (Icc (0:ℝ) 1 ×ˢ univ) := by
  rw [← modelChambers_cover hcover]
  apply finiteOpenGlue_continuousOn_prod (modelChambers_open f I w r c) (modelChambers_disjoint hd)
  intro j
  have hpar : Continuous (fun p : ℝ × levelFibre f w r => (p.1,p.2.val.1,p.2.val.2)) :=
    continuous_fst.prodMk ((continuous_subtype_val.comp continuous_snd).fst.prodMk
      (continuous_subtype_val.comp continuous_snd).snd)
  have hmap : MapsTo (fun p : ℝ × levelFibre f w r => (p.1,p.2.val.1,p.2.val.2))
      (Icc (0:ℝ) 1 ×ˢ modelChambers f I w r c j)
      {p : ℝ × E × M | p.1 ∈ Icc 0 1 ∧ ‖p.2.1‖ = 1 ∧
        p.2.1 ∈ signChamber (activeVectors f I) (c j) ∧ p.2.2 ∈ matrixFibre p.2.1} :=
    fun p hp => ⟨hp.1,p.2.property.1.1,interior_subset hp.2,p.2.property.2⟩
  exact ContinuousOn.comp' (g := fun p : ℝ × E × M => fibreHomotopy f I (c j) (g j) p.1 p.2.1 p.2.2)
    (f := fun p : ℝ × levelFibre f w r => (p.1,p.2.val.1,p.2.val.2))
    (hf.fibreHomotopy_continuousOn hI (hc j) (hcn j) (g j) (hg j)) hpar.continuousOn hmap

lemma Admissible.level_hits_compact {f : E → ι → ℝ} (hf : Admissible f)
    {I : Finset ι} (hI : I.Nonempty) {w : E} {r : ι → ℝ} (c : κ → E)
    (hc : ∀ j, c j ∈ commonPositiveCone f I) (hcn : ∀ j, ‖c j‖ = 1)
    (hd : Pairwise (fun i j => Disjoint (interior (signChamber (activeVectors f I) (c i)))
      (interior (signChamber (activeVectors f I) (c j)))))
    (hcover : orientedLevel f w r ⊆ ⋃ j, interior (signChamber (activeVectors f I) (c j)))
    (g : κ → M → EuclideanSpace ℝ ↥(Iᶜ : Finset ι)) (hg : ∀ j, Continuous (g j))
    (z : EuclideanSpace ℝ ↥(Iᶜ : Finset ι)) :
    IsCompact {A : traceSphere ν | ∃ p : levelFibre f w r, balancedModel p = A ∧
      ∃ t ∈ Icc (0:ℝ) 1, levelHomotopy f I w r c g (t,p) = z} := by
  let : CompactSpace (levelFibre f w r) := isCompact_iff_compactSpace.mp (hf.levelFibre_compact w r)
  exact compact_target_hits balancedModel (balancedModel_continuous f w r)
    (levelHomotopy f I w r c g) (hf.levelHomotopy_continuousOn hI c hc hcn hd hcover g hg) z

end LevelModel
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

omit [Nonempty ν] in
lemma negativeFibre_continuousOn {X : Type*} [TopologicalSpace X]
    (A : X → M) (hA : Continuous A) (hSA : ∀ x, IsSelfAdjoint (A x)) :
    ContinuousOn (fun x => negativeFibre (A x)) {x | Matrix.trace (A x)⁻ ≠ 0} := by
  have hP : Continuous (fun x => (A x)⁻) :=
    matrix_negPart_continuousOn.comp_continuous hA hSA
  exact ((matrix_trace_continuous.comp hP).continuousOn.inv₀ (fun _ hx => hx)).smul hP.continuousOn

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
local notation "op" => Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)

omit [Nonempty ν] in
lemma Admissible.purityChart_isOpen {f : E → ι → ℝ} (hf : Admissible f)
    (I : Finset ι) (w c : E) {X : Type*} [TopologicalSpace X]
    (A : X → M) (hA : Continuous A) (hSA : ∀ x, IsSelfAdjoint (A x)) :
    IsOpen (A ⁻¹' purityChart f I w c) := by
  have hop : Continuous (fun x => op (A x)⁺ w) :=
    (((op).toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional).comp
      (matrix_posPart_continuousOn.comp_continuous hA hSA)).clm_apply continuous_const
  have hopen : IsOpen {x | op (A x)⁺ w ≠ 0} := (isClosed_eq hop continuous_const).isOpen_compl
  have hrep := lineRepresentative_continuousOn A hA hSA w
  have hpre : IsOpen ({x | op (A x)⁺ w ≠ 0} ∩
      (fun x => lineRepresentative w (A x)) ⁻¹'
      (commonPositiveCone f I ∩ interior (signChamber (activeVectors f I) c))) :=
    hrep.isOpen_inter_preimage hopen ((hf.commonPositiveCone_isOpen I).inter isOpen_interior)
  have hn : IsOpen {x | 0 < Matrix.trace (A x)⁻} := isOpen_lt continuous_const
    (matrix_trace_continuous.comp (matrix_negPart_continuousOn.comp_continuous hA hSA))
  have he : A ⁻¹' purityChart f I w c =
      ({x | IsUnit (A x) ∧ HasPositiveLine (A x)} ∩ {x | 0 < Matrix.trace (A x)⁻}) ∩
        ({x | op (A x)⁺ w ≠ 0} ∩ (fun x => lineRepresentative w (A x)) ⁻¹'
          (commonPositiveCone f I ∩ interior (signChamber (activeVectors f I) c))) := by
    ext x
    simp only [purityChart,mem_preimage,mem_ofPred_eq,mem_inter_iff]
    tauto
  rw [he]
  exact ((positive_line_isOpen A hA hSA).inter hn).inter hpre

omit [Fintype ι] in
omit [Nonempty ν] in
lemma purityChart_unit {f : E → ι → ℝ} {I : Finset ι} {w c : E} {A : M}
    (hA : A ∈ purityChart f I w c) : ‖lineRepresentative w A‖ = 1 :=
  lineRepresentative_norm hA.2.2.1

omit [Fintype ι] in
lemma purityChart_fibre {f : E → ι → ℝ} {I : Finset ι} {w c : E} {A : M}
    (hA : A ∈ purityChart f I w c) : negativeFibre A ∈ matrixFibre (lineRepresentative w A) :=
  negativeFibre_mem hA.2.1 hA.2.2.1 hA.2.2.2.1

end PurityChart
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

lemma split_unit_of_fibre_unit {u : E} (hu : ‖u‖ = 1) {Q : M} (hQ : 0 ≤ Q)
    (hQu : op Q u = 0) {lam mu : ℝ} (hl : 0 < lam) (hm : 0 < mu)
    (hunit : IsUnit (rankOne u + Q)) : IsUnit (lam • rankOne u - mu • Q) := by
  apply (isUnit_map_iff (op) _).mp
  apply ContinuousLinearMap.isUnit_iff_bijective.mpr
  have hi : Function.Injective (op (lam • rankOne u - mu • Q)) := by
    apply (LinearMap.ker_eq_bot).mp
    rw [Submodule.eq_bot_iff]
    intro v hv
    have hv0 : op (lam • rankOne u - mu • Q) v = 0 := hv
    have hi := congrArg (fun b : E => ⟪u,b⟫) hv0
    have hQv : ⟪u,op Q v⟫ = 0 := matrix_image_orthogonal_kernel hQ.isSelfAdjoint hQu v
    simp only [map_sub,map_smul,sub_apply,smul_apply,
      rankOne_action,inner_sub_right,inner_smul_right,real_inner_self_eq_norm_sq,hu,one_pow,
      mul_one,hQv,mul_zero,sub_zero,inner_zero_right] at hi
    have huv : ⟪u,v⟫ = 0 := (mul_eq_zero.mp hi).resolve_left (ne_of_gt hl)
    have hzero : op Q v = 0 := by
      simp only [map_sub,map_smul,sub_apply,smul_apply,
        rankOne_action,huv,zero_smul,smul_zero,zero_sub,neg_eq_zero] at hv0
      exact (smul_eq_zero.mp hv0).resolve_left (ne_of_gt hm)
    have huop := ContinuousLinearMap.isUnit_iff_bijective.mp (hunit.map (op).toMonoidHom)
    apply huop.1
    change op (rankOne u + Q) v = op (rankOne u + Q) 0
    simp only [map_add,add_apply,rankOne_action,huv,zero_smul,hzero,add_zero,map_zero]
  exact ⟨hi,(LinearMap.injective_iff_surjective).mp hi⟩

omit [Nonempty ν] in
lemma lineRepresentative_split {u w : E} (hu : ‖u‖ = 1) {A : M} {lam : ℝ}
    (hl : 0 < lam) (he : A⁺ = lam • rankOne u) (hwu : 0 < ⟪w,u⟫) :
    lineRepresentative w A = u := by
  have hp : 0 < lam * ⟪u,w⟫ := mul_pos hl (by simpa only [real_inner_comm] using hwu)
  have hop : op A⁺ w = (lam * ⟪u,w⟫) • u := by
    rw [he,map_smul,smul_apply,rankOne_action,smul_smul]
  rw [lineRepresentative,hop,norm_smul,Real.norm_eq_abs,abs_of_pos hp,hu,mul_one,smul_smul,inv_mul_cancel₀ (ne_of_gt hp),one_smul]

lemma balancedFibre_chart {ι : Type*} [Fintype ι] {f : E → ι → ℝ} {I : Finset ι}
    {w c u : E} (hu : ‖u‖ = 1) (hwu : 0 < ⟪w,u⟫)
    (huc : u ∈ commonPositiveCone f I)
    (hch : u ∈ interior (signChamber (activeVectors f I) c)) {Q : M}
    (hQ : Q ∈ matrixFibre u) (hunit : IsUnit (rankOne u + Q)) :
    ((1/2:ℝ) • rankOne u - (1/2:ℝ) • Q) ∈ purityChart f I w c := by
  have hp : (0:ℝ) < 1/2 := by norm_num
  obtain ⟨he,hn⟩ := rankOne_split_parts hQ.1 hQ.2.2 hp.le hp.le
  have hline : HasPositiveLine ((1/2:ℝ) • rankOne u - (1/2:ℝ) • Q) := ⟨u,hu,1/2,hp,he⟩
  have hrep := lineRepresentative_split hu hp he hwu
  refine ⟨split_unit_of_fibre_unit hu hQ.1 hQ.2.2 hp hp hunit,hline,
    unit_rankOne_inner_nonzero hline hu hp he (ne_of_gt hwu),?_,?_,?_⟩
  · rw [hn,Matrix.trace_smul,hQ.2.1,smul_eq_mul,mul_one]; exact hp
  · rwa [hrep]
  · rwa [hrep]

end BalancedChart
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

omit [Nonempty ν] in
lemma Admissible.mixedHomotopy_nonzero {f : E → ι → ℝ} (hf : Admissible f) {I : Finset ι}
    (hI : I.Nonempty) {w c : E} (g : M → EuclideanSpace ℝ ↥(Iᶜ : Finset ι))
    (t : ℝ) {A : M} (hA : A ∈ purityChart f I w c) : mixedHomotopy f I w c g t A ≠ 0 :=
  blockVector_nonzero hI (hasPositiveLine_trace_pos hA.2.1)
    (hf.cone_unit_positive (purityChart_unit hA) hA.2.2.2.2.1) _

lemma Admissible.mixedHomotopy_continuousOn {f : E → ι → ℝ} (hf : Admissible f)
    {I : Finset ι} (hI : I.Nonempty) {w c : E} (hc : c ∈ commonPositiveCone f I) (hcn : ‖c‖ = 1)
    (g : M → EuclideanSpace ℝ ↥(Iᶜ : Finset ι)) (hg : Continuous g) :
    ContinuousOn (fun p : ℝ × traceSphere ν => mixedHomotopy f I w c g p.1 p.2.val)
      (Icc (0:ℝ) 1 ×ˢ {A : traceSphere ν | A.val ∈ purityChart f I w c}) := by
  let S : Set (ℝ × traceSphere ν) := Icc (0:ℝ) 1 ×ˢ {A : traceSphere ν | A.val ∈ purityChart f I w c}
  have hA : Continuous (fun p : ℝ × traceSphere ν => p.2.val) := continuous_subtype_val.comp continuous_snd
  have hSA : ∀ p : ℝ × traceSphere ν, IsSelfAdjoint p.2.val := fun p => p.2.property.1
  have hu : ContinuousOn (fun p : ℝ × traceSphere ν => lineRepresentative w p.2.val) S :=
    (lineRepresentative_continuousOn _ hA hSA w).mono (fun p hp => hp.2.2.2.1)
  have hQ : ContinuousOn (fun p : ℝ × traceSphere ν => negativeFibre p.2.val) S :=
    (negativeFibre_continuousOn _ hA hSA).mono (fun p hp => ne_of_gt hp.2.2.2.2.1)
  have htuple : ContinuousOn (fun p : ℝ × traceSphere ν =>
      (p.1,lineRepresentative w p.2.val,negativeFibre p.2.val)) S :=
    continuous_fst.continuousOn.prodMk (hu.prodMk hQ)
  have hF : ContinuousOn (fun p : ℝ × traceSphere ν =>
      fibreHomotopy f I c g p.1 (lineRepresentative w p.2.val) (negativeFibre p.2.val)) S :=
    ContinuousOn.comp' (g := fun p : ℝ × E × M => fibreHomotopy f I c g p.1 p.2.1 p.2.2)
      (f := fun p : ℝ × traceSphere ν => (p.1,lineRepresentative w p.2.val,negativeFibre p.2.val))
      (hf.fibreHomotopy_continuousOn hI hc hcn g hg) htuple
      (fun p hp => ⟨hp.1,purityChart_unit hp.2,interior_subset hp.2.2.2.2.2.2,purityChart_fibre hp.2⟩)
  have hl : Continuous (fun p : ℝ × traceSphere ν => Matrix.trace p.2.val⁺) :=
    matrix_trace_continuous.comp (matrix_posPart_continuousOn.comp_continuous hA hSA)
  have hm : Continuous (fun p : ℝ × traceSphere ν => Matrix.trace p.2.val⁻) :=
    matrix_trace_continuous.comp (matrix_negPart_continuousOn.comp_continuous hA hSA)
  have hfC : Continuous f := continuous_pi (fun i => (hf.smooth i).continuous)
  exact blockVector_continuousOn I hl.continuousOn (hfC.comp_continuousOn hu) hm.continuousOn hF

end MixedHomotopy
end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Projectors_ChartSurgery
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
open Set
section ChartSurgery
variable {ν ι κ : Type*} [Fintype ν] [LinearOrder ν] [Nonempty ν] [Fintype ι] [DecidableEq ι] [Fintype κ]
local notation "E" => EuclideanSpace ℝ ν
local notation "M" => Matrix ν ν ℝ
local notation "Y" => EuclideanSpace ℝ ι

lemma Admissible.chart_surgery_impossible_oai {f : E → ι → ℝ} (hf : Admissible f)
    (hdim : Fintype.card (UpperTriangle ν) = Fintype.card ι) (hn : 1 < Fintype.card ι)
    {I : Finset ι} (hI : I.Nonempty) [Nonempty ↥(Iᶜ : Finset ι)]
    (hmax : ∀ u : E, ‖u‖ = 1 → I ⊆ positiveSupport f u → positiveSupport f u = I)
    {w : E} (hw : ‖w‖ = 1) (hwi : ∀ i ∈ I, 0 < f w i)
    {r : ι → ℝ} (hr : ∀ i ∈ I, 0 < r i) (hro : ∀ i ∉ I, r i = 0) (hrs : ∑ i, r i = 1)
    (c : κ → E) (hc : ∀ j, c j ∈ commonPositiveCone f I) (hcn : ∀ j, ‖c j‖ = 1)
    (hd : Pairwise (fun i j => Disjoint (interior (signChamber (activeVectors f I) (c i)))
      (interior (signChamber (activeVectors f I) (c j)))))
    (hcover : orientedLevel f w r ⊆ ⋃ j, interior (signChamber (activeVectors f I) (c j)))
    {ε : ℝ} (hε : 0 < ε) (g : κ → M → EuclideanSpace ℝ ↥(Iᶜ : Finset ι))
    (hg : ∀ j, Continuous (g j)) (hgs : ∀ j, ∀ Q ∈ matrixFibre (c j), ∑ i, g j Q i = 1)
    (hge : ∀ j, ∀ Q ∈ matrixFibre (c j), ‖g j Q - negativeCoordinates f I Q‖ < ε)
    (z : EuclideanSpace ℝ ↥(Iᶜ : Finset ι)) (hz : ∀ i, ε < z i) (hzs : ∑ i, z i = 1)
    (hgm : ∀ j, ∀ Q ∈ matrixFibre (c j), g j Q ≠ z) : False := by
  classical
  let S : κ → Set (traceSphere ν) := fun j => {A | A.val ∈ purityChart f I w (c j)}
  let U : Set (traceSphere ν) := ⋃ j, S j
  let C : Set (traceSphere ν) := {A | ∃ p : levelFibre f w r, balancedModel p = A ∧
    ∃ t ∈ Icc (0:ℝ) 1, levelHomotopy f I w r c g (t,p) = z}
  let K : ℝ × traceSphere ν → Y := finiteOpenGlue (fun j => {p | p.2 ∈ S j})
    (fun j p => mixedHomotopy f I w (c j) (g j) p.1 p.2.val)
  let H : traceSphere ν → Y := fun A => WithLp.toLp 2 (signedExtension f A.val)
  let y : Y := blockVector I (1/2:ℝ) r (1/2:ℝ) z
  let B : Set Y := {v | ∃ d : ℝ, 0 < d ∧ v = d • y}
  have hSo : ∀ j, IsOpen (S j) := fun j =>
    hf.purityChart_isOpen I w (c j) Subtype.val continuous_subtype_val (fun A => A.property.1)
  have hSd : Pairwise (fun i j => Disjoint (S i) (S j)) := by
    intro i j hij
    exact Set.disjoint_left.mpr (fun A hA hB => Set.disjoint_left.mp (hd hij) hA.2.2.2.2.2 hB.2.2.2.2.2)
  have hKd : Pairwise (fun i j => Disjoint {p : ℝ × traceSphere ν | p.2 ∈ S i}
      {p : ℝ × traceSphere ν | p.2 ∈ S j}) := by
    intro i j hij
    exact Set.disjoint_left.mpr (fun p ha hb => Set.disjoint_left.mp (hSd hij) ha hb)
  have hKe (j : κ) (A : traceSphere ν) (hA : A ∈ S j) (t : ℝ) :
      K (t,A) = mixedHomotopy f I w (c j) (g j) t A.val :=
    finiteOpenGlue_eq hKd _ hA
  have hK : ContinuousOn K (Icc (0:ℝ) 1 ×ˢ U) :=
    finiteOpenGlue_continuousOn_prod hSo hSd _
      (fun j => hf.mixedHomotopy_continuousOn hI (hc j) (hcn j) (g j) (hg j))
  have hC : IsCompact C := hf.level_hits_compact hI c hc hcn hd hcover g hg z
  have hCU : C ⊆ U := by
    rintro A ⟨p,rfl,t,ht,he⟩
    obtain ⟨j,hj⟩ := mem_iUnion.mp (hcover p.property.1)
    have hF : fibreHomotopy f I (c j) (g j) t p.val.1 p.val.2 = z :=
      (levelHomotopy_eq hd g hj t).symm.trans he
    have hunit : IsUnit (rankOne p.val.1 + p.val.2) := by
      by_contra hnu
      exact hf.fibreHomotopy_boundary_misses hI (hc j) (hcn j) p.property.1.1
        (interior_subset hj) (g j) hε (hge j) z hz ht p.property.2 hnu hF
    apply mem_iUnion.mpr
    refine ⟨j,?_⟩
    exact balancedFibre_chart p.property.1.1 (hf.orientedLevel_inner_pos hI hw hwi hr p.property.1)
      (orientedLevel_cone hr p.property.1) hj p.property.2 hunit
  have hH : Continuous H := (PiLp.continuous_toLp 2 _).comp
    (hf.signedExtension_continuousOn.comp_continuous continuous_subtype_val (fun A => A.property.1))
  have hHz : ∀ A : traceSphere ν, H A ≠ 0 := by
    intro A h
    have hzero : signedExtension f A.val = 0 := WithLp.toLp_injective 2 h
    exact traceSphere_ne_zero A.property ((hf.signedExtension_eq_zero_iff A.property.1).mp hzero)
  have hK0 : ∀ A ∈ U, K (0,A) = H A := by
    intro A hA
    obtain ⟨j,hj⟩ := mem_iUnion.mp hA
    rw [hKe j A hj 0]
    exact hf.mixedHomotopy_zero hmax (g j) A.property.1 hj
  have hKz : ∀ t ∈ Icc (0:ℝ) 1, ∀ A ∈ U, K (t,A) ≠ 0 := by
    intro t ht A hA
    obtain ⟨j,hj⟩ := mem_iUnion.mp hA
    rw [hKe j A hj t]
    exact hf.mixedHomotopy_nonzero hI (g j) t hj
  have houtside : ∀ A ∉ U, H A ∉ B := by
    rintro A hAU ⟨d,hdp,he⟩
    obtain ⟨hunit,hline,hAw,hm,hlevel⟩ := hf.original_ray_level hI hmax hw hwi hr hro hrs
      (fun i => hε.trans (hz i)) hzs A.property hdp he
    obtain ⟨j,hj⟩ := mem_iUnion.mp (hcover hlevel)
    exact hAU (mem_iUnion.mpr ⟨j,hunit,hline,hAw,hm,orientedLevel_cone hr hlevel,hj⟩)
  have hhits : ∀ t ∈ Icc (0:ℝ) 1, ∀ A ∈ U, K (t,A) ∈ B → A ∈ C := by
    rintro t ht A hAU ⟨d,hdp,he⟩
    obtain ⟨j,hj⟩ := mem_iUnion.mp hAU
    rw [hKe j A hj t] at he
    obtain ⟨hl,hF,hA⟩ := hf.mixedHomotopy_hit hI hmax (hc j) (hcn j) (g j) (hgs j)
      hro hrs hzs ht hdp A.property hj he
    let p : levelFibre f w r := ⟨(lineRepresentative w A.val,negativeFibre A.val),hl,purityChart_fibre hj⟩
    refine ⟨p,Subtype.ext hA.symm,t,ht,?_⟩
    exact (levelHomotopy_eq hd g hj.2.2.2.2.2 t).trans hF
  have hend : ∀ A ∈ U, K (1,A) ∉ B := by
    rintro A hAU ⟨d,hdp,he⟩
    obtain ⟨j,hj⟩ := mem_iUnion.mp hAU
    rw [hKe j A hj 1] at he
    obtain ⟨-,hF,-⟩ := hf.mixedHomotopy_hit hI hmax (hc j) (hcn j) (g j) (hgs j)
      hro hrs hzs ⟨zero_le_one,le_rfl⟩ hdp A.property hj he
    rw [fibreHomotopy_one f I (hcn j) (purityChart_unit hj) (g j) (purityChart_fibre hj)] at hF
    exact hgm j _ (centeredFibre_mem (hcn j) (purityChart_unit hj) (purityChart_fibre hj)) hF
  let : CompactSpace (traceSphere ν) := isCompact_iff_compactSpace.mp traceSphere_compact
  obtain ⟨G,hG,hG0,hGz,hGm⟩ := compact_local_homotopy (isOpen_iUnion hSo) hC hCU H hH hHz
    K hK hK0 hKz B houtside hhits hend
  have hy : y ≠ 0 := blockVector_nonzero hI (by norm_num) hr z
  obtain ⟨A,d,hd,he⟩ := hf.traceHomotopy_ray hdim hn G hG hG0 hGz hy
  exact hGm A ⟨d,hd,he⟩

end ChartSurgery
end BorsukNine

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.BorsukNine.Admissible.chart_surgery_impossible_oai.{u_1, u_2, u_3} := @OAI.BorsukNine.Admissible.chart_surgery_impossible_oai.{u_1, u_2, u_3}
