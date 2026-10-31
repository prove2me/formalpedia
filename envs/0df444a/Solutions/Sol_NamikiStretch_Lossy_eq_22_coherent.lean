-- Prove2me | solution 1 for NamikiStretch.Lossy.eq_22_coherent
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T02:35:46.397788+00:00
-- url     : https://prove2.me/submissions/19b78b52-e10d-4972-b480-c5ec7491820c

import Definitions.Def_NamikiStretch_Lossy_Protocol

namespace NamikiStretch.Lossy

open MeasureTheory
open QAlgorithms.Papers.Independent.Dependency50.P39
open QAlgorithms.Papers.Independent.Frontier30.P21

lemma outcome_def' (z : ℝ × ℝ) :
    outcome z = ((z.1 : ℂ) + (z.2 : ℂ) * Complex.I) / ((Real.sqrt 2 : ℝ) : ℂ) := rfl

lemma outcome_re (z : ℝ × ℝ) : (outcome z).re = z.1 / Real.sqrt 2 := by
  dsimp [outcome]
  simp

lemma outcome_im (z : ℝ × ℝ) : (outcome z).im = z.2 / Real.sqrt 2 := by
  dsimp [outcome]
  simp

lemma star_outcome_re (z : ℝ × ℝ) : (star (outcome z)).re = z.1 / Real.sqrt 2 := by
  rw [Complex.star_def, Complex.conj_re, outcome_re]

lemma star_outcome_im (z : ℝ × ℝ) : (star (outcome z)).im = - (z.2 / Real.sqrt 2) := by
  rw [Complex.star_def, Complex.conj_im, outcome_im]

lemma normSq_alpha_sub_star_outcome (α : ℂ) (z : ℝ × ℝ) :
    Complex.normSq (α - star (outcome z)) =
      (z.1 - Real.sqrt 2 * α.re) ^ 2 / 2 + (z.2 + Real.sqrt 2 * α.im) ^ 2 / 2 := by
  rw [Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, star_outcome_re, star_outcome_im, sub_neg_eq_add]
  have hre : α.re - z.1 / Real.sqrt 2 = - (z.1 - Real.sqrt 2 * α.re) / Real.sqrt 2 := by
    have : Real.sqrt 2 ≠ 0 := by positivity
    field_simp
    ring
  have him : α.im + z.2 / Real.sqrt 2 = (z.2 + Real.sqrt 2 * α.im) / Real.sqrt 2 := by
    have : Real.sqrt 2 ≠ 0 := by positivity
    field_simp
    ring
  rw [hre, him]
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h_sq1 : (z.1 - Real.sqrt 2 * α.re) ^ 2 = (z.1 - Real.sqrt 2 * α.re) * (z.1 - Real.sqrt 2 * α.re) := by ring
  have h_sq2 : (z.2 + Real.sqrt 2 * α.im) ^ 2 = (z.2 + Real.sqrt 2 * α.im) * (z.2 + Real.sqrt 2 * α.im) := by ring
  rw [h_sq1, h_sq2]
  have hdiv1 : -(z.1 - Real.sqrt 2 * α.re) / Real.sqrt 2 * (-(z.1 - Real.sqrt 2 * α.re) / Real.sqrt 2) =
      (z.1 - Real.sqrt 2 * α.re) * (z.1 - Real.sqrt 2 * α.re) / (Real.sqrt 2 * Real.sqrt 2) := by ring
  have hdiv2 : (z.2 + Real.sqrt 2 * α.im) / Real.sqrt 2 * ((z.2 + Real.sqrt 2 * α.im) / Real.sqrt 2) =
      (z.2 + Real.sqrt 2 * α.im) * (z.2 + Real.sqrt 2 * α.im) / (Real.sqrt 2 * Real.sqrt 2) := by ring
  rw [hdiv1, hdiv2, h2]

lemma exp_factorization (ξ : ℝ) (α : ℂ) (z : ℝ × ℝ) :
    let b := (1 - ξ ^ 2) / 2
    Real.exp (-(1 - ξ ^ 2) * Complex.normSq (α - star (outcome z))) =
      Real.exp (- b * (z.1 - Real.sqrt 2 * α.re) ^ 2) *
      Real.exp (- b * (z.2 + Real.sqrt 2 * α.im) ^ 2) := by
  have h_norm := normSq_alpha_sub_star_outcome α z
  dsimp only
  rw [h_norm]
  have h_mul : -(1 - ξ ^ 2) * ((z.1 - Real.sqrt 2 * α.re) ^ 2 / 2 + (z.2 + Real.sqrt 2 * α.im) ^ 2 / 2) =
      -((1 - ξ ^ 2) / 2) * (z.1 - Real.sqrt 2 * α.re) ^ 2 + -((1 - ξ ^ 2) / 2) * (z.2 + Real.sqrt 2 * α.im) ^ 2 := by
    ring
  rw [h_mul, Real.exp_add]

lemma w_factorization (ξ : ℝ) (α : ℂ) (z : ℝ × ℝ) :
    let b := (1 - ξ ^ 2) / 2
    let f := fun x : ℝ => (b / Real.pi) * Real.exp (- b * (x - Real.sqrt 2 * α.re) ^ 2)
    let g := fun p : ℝ => Real.exp (- b * (p + Real.sqrt 2 * α.im) ^ 2)
    (1 - ξ ^ 2) / (2 * Real.pi) *
      Real.exp (-(1 - ξ ^ 2) * Complex.normSq (α - star (outcome z))) =
      f z.1 * g z.2 := by
  have h_exp := exp_factorization ξ α z
  dsimp only
  rw [h_exp]
  have h_coeff : (1 - ξ ^ 2) / (2 * Real.pi) = ((1 - ξ ^ 2) / 2) / Real.pi := by
    ring
  rw [h_coeff]
  ring

lemma b_pos {ξ : ℝ} (hξ0 : 0 < ξ) (hξ1 : ξ < 1) : 0 < (1 - ξ ^ 2) / 2 := by
  have : ξ ^ 2 < 1 := by nlinarith
  linarith

lemma integrable_f (b : ℝ) (hb : 0 < b) (c : ℝ) :
    Integrable (fun x : ℝ => (b / Real.pi) * Real.exp (- b * (x - c) ^ 2)) := by
  have h1 : Integrable (fun x : ℝ => Real.exp (- b * x ^ 2)) :=
    integrable_exp_neg_mul_sq hb
  have h2 : Integrable (fun x : ℝ => Real.exp (- b * (x - c) ^ 2)) :=
    h1.comp_sub_right c
  exact h2.const_mul (b / Real.pi)

lemma integrable_g (b : ℝ) (hb : 0 < b) (c : ℝ) :
    Integrable (fun p : ℝ => Real.exp (- b * (p + c) ^ 2)) := by
  have h1 : Integrable (fun p : ℝ => Real.exp (- b * p ^ 2)) :=
    integrable_exp_neg_mul_sq hb
  exact h1.comp_add_right c

lemma integrable_prod_fg (b : ℝ) (hb : 0 < b) (cx cy : ℝ) :
    Integrable (fun z : ℝ × ℝ =>
      ((b / Real.pi) * Real.exp (- b * (z.1 - cx) ^ 2)) *
      Real.exp (- b * (z.2 + cy) ^ 2)) := by
  have hf := integrable_f b hb cx
  have hg := integrable_g b hb cy
  have h_prod := hf.mul_prod hg
  rwa [← Measure.volume_eq_prod] at h_prod

lemma integral_f (b : ℝ) (c : ℝ) :
    ∫ x : ℝ, (b / Real.pi) * Real.exp (- b * (x - c) ^ 2) =
      (b / Real.pi) * Real.sqrt (Real.pi / b) := by
  rw [integral_const_mul]
  have h_shift : ∫ x : ℝ, Real.exp (- b * (x - c) ^ 2) = ∫ x : ℝ, Real.exp (- b * x ^ 2) :=
    integral_sub_right_eq_self (fun x => Real.exp (- b * x ^ 2)) c
  rw [h_shift, integral_gaussian b]

lemma integral_g (b : ℝ) (c : ℝ) :
    ∫ p : ℝ, Real.exp (- b * (p + c) ^ 2) =
      Real.sqrt (Real.pi / b) := by
  have h_shift : ∫ p : ℝ, Real.exp (- b * (p + c) ^ 2) = ∫ p : ℝ, Real.exp (- b * p ^ 2) :=
    integral_add_right_eq_self (fun p => Real.exp (- b * p ^ 2)) c
  rw [h_shift, integral_gaussian b]

lemma integral_prod_fg (b : ℝ) (hb : 0 < b) (cx cy : ℝ) :
    ∫ z : ℝ × ℝ,
      ((b / Real.pi) * Real.exp (- b * (z.1 - cx) ^ 2)) *
      Real.exp (- b * (z.2 + cy) ^ 2) = 1 := by
  rw [Measure.volume_eq_prod]
  have h_mul := integral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    (fun x : ℝ => (b / Real.pi) * Real.exp (- b * (x - cx) ^ 2))
    (fun p : ℝ => Real.exp (- b * (p + cy) ^ 2))
  rw [h_mul]
  rw [integral_f b cx, integral_g b cy]
  have h_pi_pos : 0 < Real.pi := Real.pi_pos
  have h_div_pos : 0 < Real.pi / b := div_pos h_pi_pos hb
  have h_sqrt_mul : Real.sqrt (Real.pi / b) * Real.sqrt (Real.pi / b) = Real.pi / b :=
    Real.mul_self_sqrt h_div_pos.le
  rw [mul_assoc, h_sqrt_mul]
  have hb_ne : b ≠ 0 := hb.ne'
  have hpi_ne : Real.pi ≠ 0 := h_pi_pos.ne'
  field_simp

end NamikiStretch.Lossy

open NamikiStretch.Lossy
open MeasureTheory
open QAlgorithms.Papers.Independent.Dependency50.P39
open QAlgorithms.Papers.Independent.Frontier30.P21

theorem solution (ξ : ℝ) (hξ0 : 0 < ξ) (hξ1 : ξ < 1) (α : ℂ) :
    let w : ℝ × ℝ → ℝ := fun z => (1 - ξ ^ 2) / (2 * Real.pi) *
      Real.exp (-(1 - ξ ^ 2) * Complex.normSq (α - star (outcome z)))
    (Integrable w ∧ ∫ z : ℝ × ℝ, w z = 1) ∧
    ∀ m n : ℕ, Integrable (fun z => (w z : ℂ) * coherentDensity α m n) ∧
      ∫ z : ℝ × ℝ, (w z : ℂ) * coherentDensity α m n = coherentDensity α m n := by
  intro w
  have hb : 0 < (1 - ξ ^ 2) / 2 := b_pos hξ0 hξ1
  have hw_eq : w = fun z : ℝ × ℝ =>
      (((1 - ξ ^ 2) / 2 / Real.pi) * Real.exp (- ((1 - ξ ^ 2) / 2) * (z.1 - Real.sqrt 2 * α.re) ^ 2)) *
      Real.exp (- ((1 - ξ ^ 2) / 2) * (z.2 + Real.sqrt 2 * α.im) ^ 2) := by
    funext z
    exact w_factorization ξ α z
  have hw_int : Integrable w := by
    rw [hw_eq]
    exact integrable_prod_fg ((1 - ξ ^ 2) / 2) hb (Real.sqrt 2 * α.re) (Real.sqrt 2 * α.im)
  have hw_val : ∫ z : ℝ × ℝ, w z = 1 := by
    rw [hw_eq]
    exact integral_prod_fg ((1 - ξ ^ 2) / 2) hb (Real.sqrt 2 * α.re) (Real.sqrt 2 * α.im)
  refine ⟨⟨hw_int, hw_val⟩, fun m n => ?_⟩
  refine ⟨?_, ?_⟩
  · exact hw_int.ofReal.mul_const (coherentDensity α m n)
  · rw [integral_mul_const, integral_complex_ofReal, hw_val]
    push_cast
    rw [one_mul]
