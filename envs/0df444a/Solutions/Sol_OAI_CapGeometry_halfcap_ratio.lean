-- Prove2me | solution 1 for OAI.CapGeometry.halfcap_ratio
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T14:49:54.690549+00:00
-- url     : https://prove2.me/submissions/33bd0a98-6a94-4174-9fe1-287494683027

import Mathlib
import Definitions.Def_OAIQ16Cd002

section
-- module Solutions.OAIQ16_CD.Compat
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_SphericalLaw
attribute [-instance] _root_.OAI.CapCost.intensity_finite _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal

namespace SphericalLaw
open Set MeasureTheory Metric
open scoped ENNReal Pointwise

lemma continuous_act {n : ℕ} (e : Space n ≃ₗᵢ[ℝ] Space n) : Continuous (act e) :=
  (e.continuous.comp continuous_subtype_val).subtype_mk _

lemma cone_preimage {n : ℕ} (e : Space n ≃ₗᵢ[ℝ] Space n) (S : Set (Sphere n)) :
    Ioo (0 : ℝ) 1 • ((↑) '' (act e ⁻¹' S)) =
      e ⁻¹' (Ioo (0 : ℝ) 1 • ((↑) '' S)) := by
  ext y
  constructor
  · rintro ⟨r, hr, x, hx, rfl⟩
    obtain ⟨u, hu, rfl⟩ := hx
    exact ⟨r, hr, e u.val, ⟨act e u, hu, rfl⟩, (e.map_smul r u.val).symm⟩
  · intro hy
    obtain ⟨r, hr, x, hx, he⟩ := hy
    obtain ⟨u, hu, rfl⟩ := hx
    refine ⟨r, hr, e.symm u.val, ?_, ?_⟩
    · refine ⟨act e.symm u, ?_, rfl⟩
      change act e (act e.symm u) ∈ S
      have hh : act e (act e.symm u) = u := Subtype.ext (e.apply_symm_apply u.val)
      simpa only [hh] using hu
    · apply e.injective
      rw [e.map_smul, e.apply_symm_apply]
      exact he

lemma invariant {n : ℕ} (e : Space n ≃ₗᵢ[ℝ] Space n) (S : Set (Sphere n))
    (hS : MeasurableSet S) : σ n (act e ⁻¹' S) = σ n S := by
  simp only [σ, Measure.smul_apply]
  congr 1
  rw [Measure.toSphere_apply' _ ((continuous_act e).measurable hS),
    Measure.toSphere_apply' _ hS, cone_preimage]
  congr 1
  change volume (e.toHomeomorph ⁻¹' (Ioo (0:ℝ) 1 • ((↑) '' S))) = _
  rw [← e.toHomeomorph.measurableEmbedding.map_apply]
  exact congrArg (fun μ : Measure (Space n) => μ (Ioo (0:ℝ) 1 • ((↑) '' S)))
    e.measurePreserving.map_eq

lemma positive_open {n : ℕ} [NeZero n] (U : Set (Sphere n))
    (hU : IsOpen U) (hne : U.Nonempty) : 0 < σ n U := by
  rw [σ, Measure.smul_apply, smul_eq_mul]
  apply ENNReal.mul_pos
  · exact ENNReal.inv_ne_zero.mpr (measure_ne_top _ _)
  · exact hU.measure_ne_zero (volume : Measure (Space n)).toSphere hne

end SphericalLaw

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_ConeStretch
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace ConeStretch
open Set MeasureTheory Metric
open scoped ENNReal Pointwise

lemma stretch_apply {n : ℕ} (i : Fin n) (k : ℝ) (x : Space n) (j : Fin n) :
    stretch i k x j = (if j = i then k else 1) * x j := by
  simp [stretch, Matrix.toLpLin_apply, Matrix.mulVec_diagonal]

lemma stretch_det {n : ℕ} (i : Fin n) (k : ℝ) :
    LinearMap.det (stretch i k) = k := by
  rw [stretch, Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.det_toLin,
    Matrix.det_diagonal]
  classical
  simp

lemma norm_sq {n : ℕ} (x : Space n) : ‖x‖^2 = ∑ i, (x i)^2 := by
  simpa [Real.norm_eq_abs, sq_abs] using PiLp.norm_sq_eq_of_L2 (fun _ : Fin n => ℝ) x

lemma stretch_norm_sq {n : ℕ} (i : Fin n) (k : ℝ) (x : Space n) :
    ‖stretch i k x‖^2 = ‖x‖^2 + (k^2-1)*(x i)^2 := by
  classical
  rw [norm_sq, norm_sq]
  simp only [stretch_apply]
  calc
    _ = ∑ j : Fin n, ((x j)^2 + if j = i then (k^2-1)*(x i)^2 else 0) := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases h : j = i
      · subst j; simp; ring
      · simp [h]
    _ = _ := by simp [Finset.sum_add_distrib]

lemma coordinate_sq_le {n : ℕ} (i : Fin n) (x : Space n) : (x i)^2 ≤ ‖x‖^2 := by
  rw [norm_sq]
  exact Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)

lemma stretch_norm_bounds {n : ℕ} (i : Fin n) {k : ℝ} (hk : 1 ≤ k) (x : Space n) :
    ‖x‖ ≤ ‖stretch i k x‖ ∧ ‖stretch i k x‖ ≤ k*‖x‖ := by
  have hsq := stretch_norm_sq i k x
  have hcoord := coordinate_sq_le i x
  have hk0 : 0 ≤ k := by linarith
  have hk2 : 0 ≤ k^2-1 := by nlinarith
  have hmul := mul_nonneg hk2 (sq_nonneg (x i))
  have hmul2 := mul_nonneg hk2 (sub_nonneg.mpr hcoord)
  constructor
  · nlinarith [norm_nonneg x, norm_nonneg (stretch i k x)]
  · nlinarith [norm_nonneg x, norm_nonneg (stretch i k x), mul_nonneg hk0 (norm_nonneg x)]

lemma stretch_inverse {n : ℕ} (i : Fin n) {k : ℝ} (hk : k ≠ 0) (x : Space n) :
    stretch i k (stretch i k⁻¹ x) = x := by
  ext j
  simp only [stretch_apply]
  split_ifs <;> simp [hk]

lemma threshold_iff {a b x t s k : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (ht : 0 < t) (hs : 0 < s) (hs1 : s < 1) (hk : 0 < k)
    (hrel : (k^2*(1-s^2)+s^2)*t^2 = s^2)
    (hnorm : b^2 = a^2 + (k^2-1)*x^2) :
    s*b < k*x ↔ t*a < x := by
  have hfac : 0 < k^2*(1-s^2)+s^2 := by
    have : 0 < 1-s^2 := by nlinarith
    positivity
  have heq : (k*x)^2-(s*b)^2 = (k^2*(1-s^2)+s^2)*(x^2-(t*a)^2) := by
    calc
      _ = (k^2*(1-s^2)+s^2)*x^2-s^2*a^2 := by rw [mul_pow, mul_pow, hnorm]; ring
      _ = _ := by linear_combination a^2*hrel
  by_cases hx : 0 < x
  · have hkx : 0 ≤ k*x := le_of_lt (mul_pos hk hx)
    rw [← sq_lt_sq₀ (mul_nonneg hs.le hb) hkx,
      ← sq_lt_sq₀ (mul_nonneg ht.le ha) hx.le]
    have hh : 0 < (k^2*(1-s^2)+s^2)*(x^2-(t*a)^2) ↔ 0 < x^2-(t*a)^2 :=
      mul_pos_iff_of_pos_left hfac
    simpa only [← heq, sub_pos] using hh
  · have hx0 : x ≤ 0 := le_of_not_gt hx
    have h1 := mul_nonneg hs.le hb
    have h2 := mul_nonneg ht.le ha
    have h3 := mul_nonpos_of_nonneg_of_nonpos hk.le hx0
    constructor <;> intro h <;> linarith

lemma stretch_threshold {n : ℕ} (i : Fin n) {t s k : ℝ}
    (ht : 0 < t) (hs : 0 < s) (hs1 : s < 1) (hk : 0 < k)
    (hrel : (k^2*(1-s^2)+s^2)*t^2 = s^2) (x : Space n) :
    s*‖stretch i k x‖ < (stretch i k x) i ↔ t*‖x‖ < x i := by
  rw [stretch_apply, ite_eq_left rfl]
  exact threshold_iff (norm_nonneg _) (norm_nonneg _) ht hs hs1 hk hrel
    (stretch_norm_sq i k x)

lemma stretch_cone_lower_norm {n : ℕ} (i : Fin n) {t k r : ℝ}
    (ht : 0 < t) (hk : 1 ≤ k) (hr : 0 ≤ r)
    (hrel : r^2 = 1+(k^2-1)*t^2) {x : Space n} (hx : t*‖x‖ < x i) :
    r*‖x‖ ≤ ‖stretch i k x‖ := by
  have hxi : 0 < x i := lt_of_le_of_lt (mul_nonneg ht.le (norm_nonneg x)) hx
  have hx2 : (t*‖x‖)^2 ≤ (x i)^2 := by
    exact (sq_le_sq₀ (mul_nonneg ht.le (norm_nonneg x)) hxi.le).mpr hx.le
  have hk2 : 0 ≤ k^2-1 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hx2 hk2
  have hsq := stretch_norm_sq i k x
  have hrx := mul_nonneg hr (norm_nonneg x)
  have hh : (r*‖x‖)^2 = ‖x‖^2+(k^2-1)*(t*‖x‖)^2 := by
    rw [mul_pow, hrel]; ring
  nlinarith [norm_nonneg (stretch i k x)]

lemma cone_smul {n : ℕ} (i : Fin n) (t : ℝ) {R : ℝ} (hR : 0 < R) :
    cone i t R = R • cone i t 1 := by
  ext y
  constructor
  · intro hy
    refine ⟨R⁻¹ • y, ?_, by simp [hR.ne']⟩
    change 0 < ‖R⁻¹ • y‖ ∧ ‖R⁻¹ • y‖ < 1 ∧ t*‖R⁻¹ • y‖ < (R⁻¹ • y) i
    simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR), PiLp.smul_apply,
      smul_eq_mul]
    change 0 < ‖y‖ ∧ ‖y‖ < R ∧ t*‖y‖ < y i at hy
    refine ⟨mul_pos (inv_pos.mpr hR) hy.1, ?_, ?_⟩
    · nlinarith [mul_lt_mul_of_pos_left hy.2.1 (inv_pos.mpr hR), inv_mul_cancel₀ hR.ne']
    · simpa only [mul_assoc, mul_left_comm t R⁻¹] using
        mul_lt_mul_of_pos_left hy.2.2 (inv_pos.mpr hR)
  · rintro ⟨x, hx, rfl⟩
    change 0 < ‖R • x‖ ∧ ‖R • x‖ < R ∧ t*‖R • x‖ < (R • x) i
    simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hR, PiLp.smul_apply, smul_eq_mul]
    change 0 < ‖x‖ ∧ ‖x‖ < 1 ∧ t*‖x‖ < x i at hx
    refine ⟨mul_pos hR hx.1, by nlinarith, ?_⟩
    simpa only [mul_assoc, mul_left_comm t R] using mul_lt_mul_of_pos_left hx.2.2 hR

lemma cone_volume_scale {n : ℕ} (i : Fin n) (t : ℝ) {R : ℝ} (hR : 0 < R) :
    volume (cone i t R) = ENNReal.ofReal (R^n) * volume (cone i t 1) := by
  rw [cone_smul i t hR, Measure.addHaar_smul_of_nonneg volume hR.le]
  simp [Space]

lemma stretch_cone_outer {n : ℕ} (i : Fin n) {t s k : ℝ}
    (ht : 0 < t) (hs : 0 < s) (hs1 : s < 1) (hk : 1 ≤ k)
    (hrel : (k^2*(1-s^2)+s^2)*t^2 = s^2) :
    stretch i k '' cone i t 1 ⊆ cone i s k := by
  rintro _ ⟨x, hx, rfl⟩
  have hk0 : 0 < k := lt_of_lt_of_le zero_lt_one hk
  have hn := stretch_norm_bounds i hk x
  exact ⟨lt_of_lt_of_le hx.1 hn.1,
    lt_of_le_of_lt hn.2 (by simpa using mul_lt_mul_of_pos_left hx.2.1 hk0),
    (stretch_threshold i ht hs hs1 hk0 hrel x).mpr hx.2.2⟩

lemma stretch_cone_inner {n : ℕ} (i : Fin n) {t s k r : ℝ}
    (ht : 0 < t) (hs : 0 < s) (hs1 : s < 1) (hk : 1 ≤ k) (hr : 0 < r)
    (hrel : (k^2*(1-s^2)+s^2)*t^2 = s^2)
    (hrsq : r^2 = 1+(k^2-1)*t^2) :
    cone i s r ⊆ stretch i k '' cone i t 1 := by
  intro y hy
  have hk0 : 0 < k := lt_of_lt_of_le zero_lt_one hk
  let x := stretch i k⁻¹ y
  have hxy : stretch i k x = y := stretch_inverse i hk0.ne' y
  have ht' : t*‖x‖ < x i := (stretch_threshold i ht hs hs1 hk0 hrel x).mp
    (by simpa only [hxy] using hy.2.2)
  have hlo : r*‖x‖ ≤ ‖y‖ := by
    simpa only [hxy] using stretch_cone_lower_norm i ht hk hr.le hrsq ht'
  refine ⟨x, ⟨?_, ?_, ht'⟩, hxy⟩
  · apply norm_pos_iff.mpr
    intro hx0
    have hy0 : y = 0 := by rw [← hxy, hx0, map_zero]
    have := hy.1
    simp [hy0] at this
  · have := hy.2.1
    nlinarith

lemma cone_volume_comparison {n : ℕ} (i : Fin n) {t s k r : ℝ}
    (ht : 0 < t) (hs : 0 < s) (hs1 : s < 1) (hk : 1 ≤ k) (hr : 0 < r)
    (hrel : (k^2*(1-s^2)+s^2)*t^2 = s^2)
    (hrsq : r^2 = 1+(k^2-1)*t^2) :
    ENNReal.ofReal (r^n)*volume (cone i s 1) ≤
        ENNReal.ofReal k*volume (cone i t 1) ∧
    ENNReal.ofReal k*volume (cone i t 1) ≤
        ENNReal.ofReal (k^n)*volume (cone i s 1) := by
  have hk0 : 0 < k := lt_of_lt_of_le zero_lt_one hk
  have hm : volume (stretch i k '' cone i t 1) =
      ENNReal.ofReal k*volume (cone i t 1) := by
    rw [Measure.addHaar_image_linearMap, stretch_det, abs_of_pos hk0]
  constructor
  · rw [← cone_volume_scale i s hr, ← hm]
    exact measure_mono (stretch_cone_inner i ht hs hs1 hk hr hrel hrsq)
  · rw [← cone_volume_scale i s hk0, ← hm]
    exact measure_mono (stretch_cone_outer i ht hs hs1 hk hrel)

end ConeStretch

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_CapGeometry
attribute [-instance] _root_.OAI.CapCost.intensity_finite _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace CapGeometry
open Set MeasureTheory Metric
open scoped ENNReal Pointwise
open SphericalLaw

lemma halfcap_open {n : ℕ} (x : Space n) (t : ℝ) : IsOpen (halfcap x t) :=
  isOpen_lt continuous_const (continuous_subtype_val.inner continuous_const)

lemma halfcap_measurable {n : ℕ} (x : Space n) (t : ℝ) : MeasurableSet (halfcap x t) :=
  (halfcap_open x t).measurableSet

lemma halfcap_positive {n : ℕ} [NeZero n] (u : Sphere n) {t : ℝ} (ht : t < 1) :
    0 < σ n (halfcap u.val t) := by
  apply positive_open _ (halfcap_open _ _) ⟨u, ?_⟩
  change t < inner ℝ u.val u.val
  simpa only [real_inner_self_eq_norm_sq, mem_sphere_zero_iff_norm.mp u.property, one_pow] using ht

lemma halfcap_equal_norm {n : ℕ} {x y : Space n} (hxy : ‖x‖ = ‖y‖) (t : ℝ) :
    σ n (halfcap x t) = σ n (halfcap y t) := by
  let e := (Submodule.span ℝ ({x-y} : Set (Space n)))ᗮ.reflection
  have he : e x = y := Submodule.reflection_sub hxy
  have hp : act e ⁻¹' halfcap y t = halfcap x t := by
    ext u
    change (t < inner ℝ (e u.val) y) ↔ (t < inner ℝ u.val x)
    rw [← he, e.inner_map_map]
  rw [← hp]
  exact invariant e _ (halfcap_measurable _ _)

lemma axis_inner {n : ℕ} (i : Fin n) (x : Space n) :
    inner ℝ x (axis i).val = x i := EuclideanSpace.inner_basisFun_real (Fin n) x i

lemma cone_eq {n : ℕ} (i : Fin n) (t : ℝ) :
    ConeStretch.cone i t 1 = Ioo (0 : ℝ) 1 • ((↑) '' halfcap (axis i).val t) := by
  ext x
  constructor
  · intro hx
    let u : Sphere n := ⟨‖x‖⁻¹ • x, by
      rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hx.1), inv_mul_cancel₀ hx.1.ne']⟩
    refine ⟨‖x‖, ⟨hx.1, hx.2.1⟩, u.val, ⟨u, ?_, rfl⟩, ?_⟩
    · change t < inner ℝ (‖x‖⁻¹ • x) (axis i).val
      rw [inner_smul_left, map_inv₀, conj_trivial, axis_inner]
      have hh := mul_lt_mul_of_pos_left hx.2.2 (inv_pos.mpr hx.1)
      simpa only [← mul_assoc, mul_left_comm ‖x‖⁻¹ t, inv_mul_cancel₀ hx.1.ne', mul_one] using hh
    · dsimp [u]
      simp [smul_smul, hx.1.ne']
  · rintro ⟨r, hr, _, ⟨u, hu, rfl⟩, rfl⟩
    have hun : ‖u.val‖ = 1 := mem_sphere_zero_iff_norm.mp u.property
    change 0 < ‖r • u.val‖ ∧ ‖r • u.val‖ < 1 ∧ t*‖r • u.val‖ < (r • u.val) i
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr.1, hun, mul_one]
    refine ⟨hr.1, hr.2, ?_⟩
    change t < inner ℝ u.val (axis i).val at hu
    rw [axis_inner] at hu
    simpa only [PiLp.smul_apply, smul_eq_mul, mul_comm t] using mul_lt_mul_of_pos_left hu hr.1

lemma halfcap_eq_cone {n : ℕ} (i : Fin n) (t : ℝ) :
    σ n (halfcap (axis i).val t) =
      (((volume : Measure (Space n)).toSphere univ)⁻¹ * n) *
        volume (ConeStretch.cone i t 1) := by
  rw [σ, Measure.smul_apply, smul_eq_mul, Measure.toSphere_apply' _ (halfcap_measurable _ _),
    ← cone_eq]
  simp [Space, mul_assoc]

lemma halfcap_comparison {n : ℕ} (i : Fin n) {t s k r : ℝ}
    (ht : 0 < t) (hs : 0 < s) (hs1 : s < 1) (hk : 1 ≤ k) (hr : 0 < r)
    (hrel : (k^2*(1-s^2)+s^2)*t^2 = s^2)
    (hrsq : r^2 = 1+(k^2-1)*t^2) :
    ENNReal.ofReal (r^n)*σ n (halfcap (axis i).val s) ≤
        ENNReal.ofReal k*σ n (halfcap (axis i).val t) ∧
    ENNReal.ofReal k*σ n (halfcap (axis i).val t) ≤
        ENNReal.ofReal (k^n)*σ n (halfcap (axis i).val s) := by
  have hh := ConeStretch.cone_volume_comparison i ht hs hs1 hk hr hrel hrsq
  rw [halfcap_eq_cone, halfcap_eq_cone]
  constructor
  · simpa only [mul_assoc, mul_left_comm] using mul_le_mul_right hh.1
      (((volume : Measure (Space n)).toSphere univ)⁻¹ * (n : ℝ≥0∞))
  · simpa only [mul_assoc, mul_left_comm] using mul_le_mul_right hh.2
      (((volume : Measure (Space n)).toSphere univ)⁻¹ * (n : ℝ≥0∞))

lemma parameters {t s : ℝ} (ht : 0 < t) (hts : t ≤ s) (hs : s < 1) :
    1 ≤ axial t s ∧ 0 < radial t s ∧
    ((axial t s)^2*(1-s^2)+s^2)*t^2 = s^2 ∧
    (radial t s)^2 = 1+((axial t s)^2-1)*t^2 := by
  have hs0 : 0 < s := ht.trans_le hts
  have ht1 : t < 1 := hts.trans_lt hs
  have hb : 0 < 1-s^2 := by nlinarith
  have ha : 0 < 1-t^2 := by nlinarith
  have hrad : (radial t s)^2 = (1-t^2)/(1-s^2) := Real.sq_sqrt (div_pos ha hb).le
  have hr1 : 1 ≤ radial t s := by
    apply (Real.le_sqrt (by norm_num) (div_pos ha hb).le).mpr
    apply (le_div_iff₀ hb).mpr
    nlinarith
  have hr0 := zero_lt_one.trans_le hr1
  have hk1 : 1 ≤ axial t s := by
    exact one_le_mul_of_one_le_of_one_le ((one_le_div ht).mpr hts) hr1
  refine ⟨hk1, hr0, ?_, ?_⟩
  · dsimp [axial]
    rw [mul_pow, hrad]
    field_simp [ht.ne', hb.ne']
    ring
  · dsimp [axial]
    rw [mul_pow, hrad]
    field_simp [ht.ne', hb.ne']
    ring

lemma log_parameters {l u t s : ℝ} (hl : 0 < l) (hu : u < 1)
    (hlt : l ≤ t) (hts : t ≤ s) (hsu : s ≤ u) :
    l*(s-t) ≤ Real.log (radial t s) ∧
    Real.log (axial t s) ≤ (1/l+1/(1-u^2))*(s-t) := by
  have ht : 0 < t := hl.trans_le hlt
  have hs0 : 0 < s := ht.trans_le hts
  have hs1 : s < 1 := hsu.trans_lt hu
  have ht1 : t < 1 := hts.trans_lt hs1
  have hb : 0 < 1-u^2 := by have : 0 < u := hs0.trans_le hsu; nlinarith
  let H := fun x : ℝ => -Real.log (1-x^2)/2
  let G := fun x : ℝ => Real.log x + H x
  have hH (x : ℝ) (hx : x ∈ Icc l u) : HasDerivAt H (x/(1-x^2)) x := by
    have hbx : 1-x^2 ≠ 0 := by have := hl.trans_le hx.1; have := hx.2.trans_lt hu; nlinarith
    convert! ((((hasDerivAt_id x).pow 2).const_sub 1).log hbx).neg.div_const 2 using 1; dsimp; ring
  have hG (x : ℝ) (hx : x ∈ Icc l u) :
      HasDerivAt G (1/x+x/(1-x^2)) x := by
    convert! (Real.hasDerivAt_log (ne_of_gt (hl.trans_le hx.1))).add (hH x hx) using 1;
      simp [one_div]
  have hHc : ContinuousOn H (Icc l u) := fun x hx => (hH x hx).continuousAt.continuousWithinAt
  have hGc : ContinuousOn G (Icc l u) := fun x hx => (hG x hx).continuousAt.continuousWithinAt
  have hHd : DifferentiableOn ℝ H (interior (Icc l u)) :=
    fun x hx => (hH x (interior_subset hx)).differentiableAt.differentiableWithinAt
  have hGd : DifferentiableOn ℝ G (interior (Icc l u)) :=
    fun x hx => (hG x (interior_subset hx)).differentiableAt.differentiableWithinAt
  have hlo (x : ℝ) (hx : x ∈ Icc l u) : l ≤ deriv H x := by
    rw [(hH x hx).deriv]
    have hbx : 0 < 1-x^2 := by have := hl.trans_le hx.1; have := hx.2.trans_lt hu; nlinarith
    apply (le_div_iff₀ hbx).mpr
    nlinarith [mul_nonneg hl.le (sq_nonneg x), hx.1]
  have hup (x : ℝ) (hx : x ∈ Icc l u) : deriv G x ≤ 1/l+1/(1-u^2) := by
    rw [(hG x hx).deriv]
    have hx0 : 0 < x := hl.trans_le hx.1
    have hx1 : x < 1 := hx.2.trans_lt hu
    have hbx : 0 < 1-x^2 := by nlinarith
    apply add_le_add (one_div_le_one_div_of_le hl hx.1)
    calc
      x/(1-x^2) ≤ 1/(1-x^2) := div_le_div_of_nonneg_right hx1.le hbx.le
      _ ≤ 1/(1-u^2) := one_div_le_one_div_of_le hb (by nlinarith [hx.2])
  have hlow := (convex_Icc l u).mul_sub_le_image_sub_of_le_deriv hHc hHd
    (fun x hx => hlo x (interior_subset hx)) t ⟨hlt,hts.trans hsu⟩ s ⟨hlt.trans hts,hsu⟩ hts
  have hupp := (convex_Icc l u).image_sub_le_mul_sub_of_deriv_le hGc hGd
    (fun x hx => hup x (interior_subset hx)) t ⟨hlt,hts.trans hsu⟩ s ⟨hlt.trans hts,hsu⟩ hts
  have hbt : 0 < 1-t^2 := by nlinarith
  have hbs : 0 < 1-s^2 := by nlinarith
  have hrad : Real.log (radial t s) = H s-H t := by
    rw [radial, Real.log_sqrt (div_pos hbt hbs).le,
      Real.log_div hbt.ne' hbs.ne']
    dsimp [H]; ring
  have hrpos := (parameters ht hts hs1).2.1
  have hax : Real.log (axial t s) = G s-G t := by
    rw [axial, Real.log_mul (div_pos hs0 ht).ne' hrpos.ne',
      Real.log_div hs0.ne' ht.ne', hrad]
    dsimp [G]; ring
  rw [hrad, hax]
  exact ⟨hlow, hupp⟩

lemma halfcap_ratio_oai {n : ℕ} [NeZero n] (e : Sphere n) {l u t s : ℝ}
    (hl : 0 < l) (hu : u < 1) (hlt : l ≤ t) (hts : t ≤ s) (hsu : s ≤ u) :
    Real.exp (-((n:ℝ)-1)*(1/l+1/(1-u^2))*(s-t)) ≤
      (σ n).real (halfcap e.val s)/(σ n).real (halfcap e.val t) ∧
    (σ n).real (halfcap e.val s)/(σ n).real (halfcap e.val t) ≤
      Real.exp (((1/l+1/(1-u^2))-(n:ℝ)*l)*(s-t)) := by
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
  let i : Fin n := ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩
  have ht : 0 < t := hl.trans_le hlt
  have hs0 : 0 < s := ht.trans_le hts
  have hs1 : s < 1 := hsu.trans_lt hu
  have par := parameters ht hts hs1
  have hh := halfcap_comparison i ht hs0 hs1 par.1 par.2.1 par.2.2.1 par.2.2.2
  have heq (v : ℝ) : σ n (halfcap (axis i).val v) = σ n (halfcap e.val v) :=
    halfcap_equal_norm (by rw [mem_sphere_zero_iff_norm.mp (axis i).property,
      mem_sphere_zero_iff_norm.mp e.property]) v
  rw [heq s, heq t] at hh
  have hk0 : 0 < axial t s := zero_lt_one.trans_le par.1
  have hr0 : 0 < radial t s := par.2.1
  have hspos : 0 < (σ n).real (halfcap e.val s) :=
    ENNReal.toReal_pos (ne_of_gt (halfcap_positive e hs1)) (measure_ne_top _ _)
  have htpos : 0 < (σ n).real (halfcap e.val t) :=
    ENNReal.toReal_pos (ne_of_gt (halfcap_positive e (hts.trans_lt hs1))) (measure_ne_top _ _)
  have hreal1 : (radial t s)^n*(σ n).real (halfcap e.val s) ≤
      axial t s*(σ n).real (halfcap e.val t) := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)) hh.1
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hr0.le n),
      ENNReal.toReal_ofReal hk0.le, measureReal_def] using this
  have hreal2 : axial t s*(σ n).real (halfcap e.val t) ≤
      (axial t s)^n*(σ n).real (halfcap e.val s) := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)) hh.2
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hk0.le n),
      ENNReal.toReal_ofReal hk0.le, measureReal_def] using this
  have logr := log_parameters hl hu hlt hts hsu
  have hlog1 := Real.log_le_log (mul_pos (pow_pos hr0 n) hspos) hreal1
  have hlog2 := Real.log_le_log (mul_pos hk0 htpos) hreal2
  simp only [Real.log_mul (pow_pos hr0 n).ne' hspos.ne', Real.log_mul hk0.ne' htpos.ne',
    Real.log_mul (pow_pos hk0 n).ne' hspos.ne', Real.log_pow] at hlog1 hlog2
  have hnreal : 1 ≤ (n:ℝ) := by exact_mod_cast hn
  have he : Real.exp (Real.log ((σ n).real (halfcap e.val s)) -
      Real.log ((σ n).real (halfcap e.val t))) =
      (σ n).real (halfcap e.val s)/(σ n).real (halfcap e.val t) := by
    rw [Real.exp_sub, Real.exp_log hspos, Real.exp_log htpos]
  rw [← he]
  constructor
  · apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left logr.2 (sub_nonneg.mpr hnreal)]
  · apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left logr.1 (Nat.cast_nonneg n : (0:ℝ) ≤ n)]

end CapGeometry

end OAI
end

theorem solution : type_of% @OAI.CapGeometry.halfcap_ratio_oai := @OAI.CapGeometry.halfcap_ratio_oai
