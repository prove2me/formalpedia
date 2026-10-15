-- Prove2me | solution 1 for OAI.HilbertCrouzeix.convex_numericalRange
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T18:04:06.343085+00:00
-- url     : https://prove2.me/submissions/5edaf2f9-ebf4-4248-9fe8-a844d169cb17

-- Generated from openai/math@1581d4c lean/OAI/Analysis/HilbertCrouzeix/NumericalRange.lean:L185-L229
-- (upload_full_project.md Phase 4): solution for node OAI.HilbertCrouzeix.convex_numericalRange. Inline helpers are the
-- source spans of proof-only lemmas this proof needs; the node is hoisted out of its namespace
-- as a top-level `theorem solution` with the namespace re-opened.
import Mathlib
import Definitions.Def_HilbertCrouzeix
import Definitions.Def_OAI_Analysis_HilbertCrouzeix_NumericalRange

-- ---- inline helpers from OAI.Analysis.HilbertCrouzeix.NumericalRange ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open Complex Set
open scoped TensorProduct Matrix.Norms.L2Operator Classical ComplexConjugate

namespace HilbertCrouzeix

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

section Elementary
omit [CompleteSpace H]

lemma exists_unit_phase (w z : ℂ) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ (c * w).im = 0 ∧ 0 ≤ (c * z).re := by
  have he : ∃ c : ℂ, ‖c‖ = 1 ∧ (c * w).im = 0 := by
    by_cases hw : w = 0
    · exact ⟨1, norm_one, by simp [hw]⟩
    let c : ℂ := (‖w‖ : ℂ)⁻¹ * conj w
    refine ⟨c, ?_, ?_⟩
    · simp [c, norm_inv, norm_ne_zero_iff.mpr hw]
    · simp only [c, mul_assoc, ← Complex.normSq_eq_conj_mul_self]
      simp
  obtain ⟨c, hc, him⟩ := he
  by_cases hre : 0 ≤ (c * z).re
  · exact ⟨c, hc, him, hre⟩
  · exact ⟨-c, by simpa using hc, by simpa only [neg_mul, Complex.neg_im, neg_eq_zero] using him,
      by simpa using (le_of_not_ge hre)⟩

lemma quadratic_cross_im (T : H →L[ℂ] H) (x y : H) (c : ℂ)
    (hc : (c * (inner ℂ x (T y) - conj (inner ℂ y (T x)))).im = 0) :
    (inner ℂ x (T (c • y)) + inner ℂ (c • y) (T x)).im = 0 := by
  simp only [map_smul, inner_smul_right, inner_smul_left]
  simp only [Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.conj_re, Complex.conj_im, Complex.add_im] at *
  linear_combination hc

lemma quadratic_segment_im (T : H →L[ℂ] H) (x y : H)
    (hx : (inner ℂ x (T x)).im = 0) (hy : (inner ℂ y (T y)).im = 0)
    (hxy : (inner ℂ x (T y) + inner ℂ y (T x)).im = 0) (s t : ℝ) :
    (inner ℂ ((s : ℂ) • x + (t : ℂ) • y)
      (T ((s : ℂ) • x + (t : ℂ) • y))).im = 0 := by
  have heq : inner ℂ ((s : ℂ) • x + (t : ℂ) • y)
      (T ((s : ℂ) • x + (t : ℂ) • y)) =
      (s : ℂ)^2 * inner ℂ x (T x) + (s : ℂ) * (t : ℂ) *
        (inner ℂ x (T y) + inner ℂ y (T x)) + (t : ℂ)^2 * inner ℂ y (T y) := by
    simp only [map_add, map_smul, inner_add_left, inner_add_right,
      inner_smul_left, inner_smul_right, Complex.conj_ofReal]
    ring
  rw [heq]
  simp only [Complex.add_im, Complex.mul_im, Complex.mul_re, ← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_im] at *
  linear_combination s * t * hxy + s ^ 2 * hx + t ^ 2 * hy

lemma unit_segment_ne_zero (x y : H) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hxy : 0 ≤ (inner ℂ x y).re) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (((1 - t : ℝ) : ℂ) • x + (t : ℂ) • y) ≠ 0 := by
  intro hz
  have hn := norm_add_sq (𝕜 := ℂ) (((1 - t : ℝ) : ℂ) • x) ((t : ℂ) • y)
  simp only [hz, norm_zero, zero_pow (by decide : 2 ≠ 0), norm_smul, hx, hy,
    mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1,
    abs_of_nonneg (sub_nonneg.mpr ht.2), inner_smul_left, inner_smul_right,
    Complex.conj_ofReal] at hn
  have hp : 0 ≤ (1 - t) * t * (inner ℂ x y).re :=
    mul_nonneg (mul_nonneg (sub_nonneg.mpr ht.2) ht.1) hxy
  change 0 = (1 - t) ^ 2 + 2 * ((t : ℂ) * (((1 - t : ℝ) : ℂ) * inner ℂ x y)).re + t ^ 2 at hn
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_im, zero_mul, add_zero, sub_zero] at hn
  nlinarith [sq_nonneg (1 - 2 * t)]

lemma zero_mem_numericalRange_of_opposite (T : H →L[ℂ] H) (x y : H)
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hxim : (inner ℂ x (T x)).im = 0) (hyim : (inner ℂ y (T y)).im = 0)
    (hxre : (inner ℂ x (T x)).re ≤ 0) (hyre : 0 ≤ (inner ℂ y (T y)).re) :
    0 ∈ numericalRange T := by
  obtain ⟨c, hc, hcim, hcre⟩ := exists_unit_phase
    (inner ℂ x (T y) - conj (inner ℂ y (T x))) (inner ℂ x y)
  let y' : H := c • y
  have hy' : ‖y'‖ = 1 := by simp [y', norm_smul, hc, hy]
  have hqy : inner ℂ y' (T y') = inner ℂ y (T y) := by
    simp only [y', map_smul, inner_smul_left, inner_smul_right, ← mul_assoc,
      RCLike.mul_conj, hc, RCLike.ofReal_one, one_pow, one_mul]
  have hcross := quadratic_cross_im T x y c hcim
  have hpos : 0 ≤ (inner ℂ x y').re := by simpa only [y', inner_smul_right] using hcre
  let v (t : ℝ) : H := (((1 - t : ℝ) : ℂ) • x + (t : ℂ) • y')
  have hv : Continuous v :=
    ((Complex.continuous_ofReal.comp (continuous_const.sub continuous_id)).smul
      continuous_const).add ((Complex.continuous_ofReal).smul continuous_const)
  let f (t : ℝ) : ℝ := (inner ℂ (v t) (T (v t))).re
  have hf : Continuous f := Complex.continuous_re.comp (hv.inner (T.continuous.comp hv))
  have hf0 : f 0 ≤ 0 := by simpa [f, v] using hxre
  have hf1 : 0 ≤ f 1 := by simpa only [f, v, sub_self, Complex.ofReal_zero,
    zero_smul, Complex.ofReal_one, one_smul, zero_add, hqy] using hyre
  obtain ⟨t, ht, hfval⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1)
    hf.continuousOn ⟨hf0, hf1⟩
  have hn : v t ≠ 0 := unit_segment_ne_zero x y' hx hy' hpos ht
  have hzero : inner ℂ (v t) (T (v t)) = 0 := by
    apply Complex.ext
    · exact hfval
    · exact quadratic_segment_im T x y' hxim (hqy ▸ hyim) hcross (1 - t) t
  refine ⟨(‖v t‖ : ℂ)⁻¹ • v t, norm_smul_inv_norm hn, ?_⟩
  simp only [map_smul, inner_smul_left, inner_smul_right, hzero, mul_zero]

end Elementary

end HilbertCrouzeix

end

end OAI

-- ---- hoisted node ----
open OAI OAI.HilbertCrouzeix
open Complex Set
open scoped TensorProduct Matrix.Norms.L2Operator Classical ComplexConjugate
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
omit [CompleteSpace H]

theorem solution (A : H →L[ℂ] H) : Convex ℝ (numericalRange A) := by
  intro z hz w hw a b ha hb hab
  by_cases hzw : z = w
  · subst w
    simpa only [← add_smul, hab, one_smul] using hz
  obtain ⟨x, hx, hxz⟩ := hz
  obtain ⟨y, hy, hyw⟩ := hw
  let δ : ℂ := w - z
  let z₀ : ℂ := a • z + b • w
  let T : H →L[ℂ] H := conj δ • (A - z₀ • (1 : H →L[ℂ] H))
  have hq (v : H) (hv : ‖v‖ = 1) :
      inner ℂ v (T v) = conj δ * (inner ℂ v (A v) - z₀) := by
    simp only [T, smul_apply, sub_apply, inner_smul_right,
      inner_sub_right, one_apply_eq_self, inner_self_eq_norm_sq_to_K, hv,
      RCLike.ofReal_one, one_pow, mul_one]
  have hxq : inner ℂ x (T x) = ((-b * normSq δ : ℝ) : ℂ) := by
    rw [hq x hx, hxz]
    calc
      conj δ * (z - z₀) = (-b : ℂ) * (conj δ * δ) := by
        have ha' : a = 1 - b := by linarith
        simp only [z₀, δ, ha', Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_one]
        ring
      _ = ((-b * normSq δ : ℝ) : ℂ) := by
        rw [← Complex.normSq_eq_conj_mul_self]
        push_cast
        rfl
  have hyq : inner ℂ y (T y) = ((a * normSq δ : ℝ) : ℂ) := by
    rw [hq y hy, hyw]
    calc
      conj δ * (w - z₀) = (a : ℂ) * (conj δ * δ) := by
        have hb' : b = 1 - a := by linarith
        simp only [z₀, δ, hb', Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_one]
        ring
      _ = ((a * normSq δ : ℝ) : ℂ) := by
        rw [← Complex.normSq_eq_conj_mul_self]
        push_cast
        rfl
  obtain ⟨v, hv, hTv⟩ := zero_mem_numericalRange_of_opposite T x y hx hy
    (by simp [hxq]) (by simp [hyq])
    (by simpa only [hxq, Complex.ofReal_re] using
      mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hb) (normSq_nonneg δ))
    (by simpa only [hyq, Complex.ofReal_re] using mul_nonneg ha (normSq_nonneg δ))
  have hδ : conj δ ≠ 0 := (map_ne_zero (starRingEnd ℂ)).mpr (sub_ne_zero.mpr (Ne.symm hzw))
  rw [hq v hv] at hTv
  exact ⟨v, hv, sub_eq_zero.mp ((mul_eq_zero.mp hTv).resolve_left hδ)⟩
