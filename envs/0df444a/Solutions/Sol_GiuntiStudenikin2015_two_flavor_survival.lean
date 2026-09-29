-- Prove2me | solution 1 for GiuntiStudenikin2015.two_flavor_survival
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-25T09:29:12.604233+00:00
-- url     : https://prove2.me/submissions/9483270d-5539-47f1-8186-f8d71a247fca

import Mathlib
import Definitions.Def_GiuntiStudenikin2015_oscillation

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem gs15_exp_neg (φ : ℝ) :
    Complex.exp (-(Complex.I * (φ : ℂ))) = (Real.cos φ : ℂ) - (Real.sin φ : ℂ) * Complex.I := by
  rw [show -(Complex.I * (φ : ℂ)) = ((-φ : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
  push_cast
  ring

theorem gs15_tf00 (θ : ℝ) : GiuntiStudenikin2015.twoFlavorMixing θ 0 0 = (Real.cos θ : ℂ) := rfl
theorem gs15_tf01 (θ : ℝ) : GiuntiStudenikin2015.twoFlavorMixing θ 0 1 = (Real.sin θ : ℂ) := rfl
theorem gs15_tf10 (θ : ℝ) : GiuntiStudenikin2015.twoFlavorMixing θ 1 0 = -(Real.sin θ : ℂ) := rfl
theorem gs15_tf11 (θ : ℝ) : GiuntiStudenikin2015.twoFlavorMixing θ 1 1 = (Real.cos θ : ℂ) := rfl

theorem gs15_hcos (m : Fin 2 → ℝ) (L E : ℝ) :
    Real.cos (m 1 ^ 2 * L / (2 * E)) * Real.cos (m 0 ^ 2 * L / (2 * E)) +
      Real.sin (m 1 ^ 2 * L / (2 * E)) * Real.sin (m 0 ^ 2 * L / (2 * E)) =
      1 - 2 * Real.sin ((m 1 ^ 2 - m 0 ^ 2) * L / (4 * E)) ^ 2 := by
  rw [← Real.cos_sub, show m 1 ^ 2 * L / (2 * E) - m 0 ^ 2 * L / (2 * E) =
    2 * ((m 1 ^ 2 - m 0 ^ 2) * L / (4 * E)) by ring, Real.cos_two_mul_eq_one_sub]

open GiuntiStudenikin2015 in
theorem solution (θ : ℝ) (hθ : 0 ≤ θ ∧ θ ≤ Real.pi / 2) (m : Fin 2 → ℝ)
    (L E : ℝ) (hE : 0 < E) (l : Fin 2) :
    oscProb (twoFlavorMixing θ) m L E l l =
      1 - Real.sin (2 * θ) ^ 2 * Real.sin ((m 1 ^ 2 - m 0 ^ 2) * L / (4 * E)) ^ 2 := by
  have hcos := gs15_hcos m L E
  have h0 := Real.sin_sq_add_cos_sq (m 0 ^ 2 * L / (2 * E))
  have h1 := Real.sin_sq_add_cos_sq (m 1 ^ 2 * L / (2 * E))
  have hθ' := Real.sin_sq_add_cos_sq θ
  unfold oscProb
  rw [Fin.sum_univ_two, gs15_exp_neg, gs15_exp_neg, Real.sin_two_mul]
  fin_cases l
  · simp only [Fin.zero_eta, Fin.isValue, gs15_tf00, gs15_tf01]
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.star_def,
      Complex.conj_re, Complex.conj_im]
    linear_combination Real.cos θ ^ 4 * h0 + Real.sin θ ^ 4 * h1 +
      2 * Real.cos θ ^ 2 * Real.sin θ ^ 2 * hcos + (Real.sin θ ^ 2 + Real.cos θ ^ 2 + 1) * hθ'
  · simp only [Fin.mk_one, Fin.isValue, gs15_tf10, gs15_tf11]
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.star_def,
      Complex.conj_re, Complex.conj_im]
    linear_combination Real.sin θ ^ 4 * h0 + Real.cos θ ^ 4 * h1 +
      2 * Real.cos θ ^ 2 * Real.sin θ ^ 2 * hcos + (Real.sin θ ^ 2 + Real.cos θ ^ 2 + 1) * hθ'
