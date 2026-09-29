-- Prove2me | solution 1 for LipariNeutrino.three_flavor_prob_expansion
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-25T08:31:10.829253+00:00
-- url     : https://prove2.me/submissions/7d65197f-341a-4573-9d54-1626a23e1995

import Mathlib
import Definitions.Def_LipariNeutrino_OscillationProbability

set_option autoImplicit false

theorem lipari_exp_neg (φ : ℝ) :
    Complex.exp (-(Complex.I * (φ : ℂ))) = (Real.cos φ : ℂ) - (Real.sin φ : ℂ) * Complex.I := by
  rw [show -(Complex.I * (φ : ℂ)) = ((-φ : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
  push_cast
  ring

theorem lipari_expand3 (z0 z1 z2 : ℂ) (φ0 φ1 φ2 : ℝ) :
    Complex.normSq (z0 * Complex.exp (-(Complex.I * (φ0 : ℂ))) +
      z1 * Complex.exp (-(Complex.I * (φ1 : ℂ))) + z2 * Complex.exp (-(Complex.I * (φ2 : ℂ)))) =
    Complex.normSq z0 + Complex.normSq z1 + Complex.normSq z2 +
    (2 * (star z0 * z1).re * Real.cos (φ1 - φ0) + 2 * (star z0 * z1).im * Real.sin (φ1 - φ0)) +
    (2 * (star z0 * z2).re * Real.cos (φ2 - φ0) + 2 * (star z0 * z2).im * Real.sin (φ2 - φ0)) +
    (2 * (star z1 * z2).re * Real.cos (φ2 - φ1) + 2 * (star z1 * z2).im * Real.sin (φ2 - φ1)) := by
  rw [lipari_exp_neg, lipari_exp_neg, lipari_exp_neg]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im, Real.cos_sub, Real.sin_sub]
  linear_combination (z0.re * z0.re + z0.im * z0.im) * Real.sin_sq_add_cos_sq φ0 +
    (z1.re * z1.re + z1.im * z1.im) * Real.sin_sq_add_cos_sq φ1 +
    (z2.re * z2.re + z2.im * z2.im) * Real.sin_sq_add_cos_sq φ2

open LipariNeutrino in
theorem solution (U : Matrix (Fin 3) (Fin 3) ℂ) (m2 : Fin 3 → ℝ) (L E : ℝ)
    (α β : Fin 3) :
    oscProb U m2 L E α β =
      (∑ j : Fin 3, ‖U β j‖ ^ 2 * ‖U α j‖ ^ 2) +
      ∑ j : Fin 3, ∑ k : Fin 3,
        if j < k then
          2 * (star (U β j) * U β k * U α j * star (U α k)).re *
              Real.cos ((m2 k - m2 j) * L / (2 * E)) +
            2 * (star (U β j) * U β k * U α j * star (U α k)).im *
              Real.sin ((m2 k - m2 j) * L / (2 * E))
        else 0 := by
  have hz : ∀ a b c d : ℂ, star (a * star b) * (c * star d) = star a * c * b * star d := by
    intro a b c d
    rw [star_mul', star_star]
    ring
  have hn : ∀ a b : ℂ, Complex.normSq (a * star b) = ‖a‖ ^ 2 * ‖b‖ ^ 2 := by
    intro a b
    rw [Complex.normSq_mul, Complex.star_def, Complex.normSq_conj, Complex.normSq_eq_norm_sq,
      Complex.normSq_eq_norm_sq]
  have hd : ∀ j k : Fin 3,
      (m2 k - m2 j) * L / (2 * E) = m2 k * L / (2 * E) - m2 j * L / (2 * E) := by
    intro j k
    ring
  have c01 : (0 : Fin 3) < 1 := by decide
  have c02 : (0 : Fin 3) < 2 := by decide
  have c12 : (1 : Fin 3) < 2 := by decide
  have n00 : ¬ (0 : Fin 3) < 0 := by decide
  have n10 : ¬ (1 : Fin 3) < 0 := by decide
  have n11 : ¬ (1 : Fin 3) < 1 := by decide
  have n20 : ¬ (2 : Fin 3) < 0 := by decide
  have n21 : ¬ (2 : Fin 3) < 1 := by decide
  have n22 : ¬ (2 : Fin 3) < 2 := by decide
  unfold LipariNeutrino.oscProb LipariNeutrino.oscAmp
  rw [Fin.sum_univ_three, lipari_expand3]
  simp only [Fin.sum_univ_three, hd, hz, hn, c01, c02, c12, n00, n10, n11, n20, n21, n22,
    ↓reduceIte]
  ring
