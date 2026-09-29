-- Prove2me | solution 1 for LipariNeutrino.two_flavor_transition_prob
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-25T09:02:27.704401+00:00
-- url     : https://prove2.me/submissions/64e7100d-cc31-4a53-b7fb-d9367f3638c7

import Mathlib
import Definitions.Def_LipariNeutrino_OscillationProbability
import Definitions.Def_LipariNeutrino_MixingMatrices

set_option autoImplicit false

theorem lipari_exp_neg (φ : ℝ) :
    Complex.exp (-(Complex.I * (φ : ℂ))) = (Real.cos φ : ℂ) - (Real.sin φ : ℂ) * Complex.I := by
  rw [show -(Complex.I * (φ : ℂ)) = ((-φ : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
  push_cast
  ring

open LipariNeutrino in
theorem solution (θ : ℝ) (m2 : Fin 2 → ℝ) (L E : ℝ) :
    oscProb (twoFlavorMix θ) m2 L E 0 1 =
      Real.sin (2 * θ) ^ 2 * Real.sin ((m2 1 - m2 0) * L / (4 * E)) ^ 2 := by
  have e00 : twoFlavorMix θ 0 0 = (Real.cos θ : ℂ) := rfl
  have e01 : twoFlavorMix θ 0 1 = (Real.sin θ : ℂ) := rfl
  have e10 : twoFlavorMix θ 1 0 = -(Real.sin θ : ℂ) := rfl
  have e11 : twoFlavorMix θ 1 1 = (Real.cos θ : ℂ) := rfl
  have hcos : Real.cos (m2 1 * L / (2 * E)) * Real.cos (m2 0 * L / (2 * E)) +
      Real.sin (m2 1 * L / (2 * E)) * Real.sin (m2 0 * L / (2 * E)) =
      1 - 2 * Real.sin ((m2 1 - m2 0) * L / (4 * E)) ^ 2 := by
    rw [← Real.cos_sub, show m2 1 * L / (2 * E) - m2 0 * L / (2 * E) =
      2 * ((m2 1 - m2 0) * L / (4 * E)) by ring, Real.cos_two_mul_eq_one_sub]
  unfold oscProb oscAmp
  rw [Fin.sum_univ_two, e10, e00, e11, e01, lipari_exp_neg, lipari_exp_neg, Real.sin_two_mul]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.star_def, Complex.conj_re,
    Complex.conj_im]
  linear_combination
    (Real.sin θ ^ 2 * Real.cos θ ^ 2) * Real.sin_sq_add_cos_sq (m2 1 * L / (2 * E)) +
    (Real.sin θ ^ 2 * Real.cos θ ^ 2) * Real.sin_sq_add_cos_sq (m2 0 * L / (2 * E)) -
    2 * Real.sin θ ^ 2 * Real.cos θ ^ 2 * hcos
