-- Prove2me | solution 1 for LipariNeutrino.three_flavor_transition_prob
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-25T09:02:27.924974+00:00
-- url     : https://prove2.me/submissions/8cbe8772-22be-4b21-9479-6b788bc1d593

import Mathlib
import Definitions.Def_LipariNeutrino_OscillationProbability

set_option autoImplicit false

theorem lipari_im_cyclic (x0 x1 x2 : ℂ) (h : x0 + x1 + x2 = 0) :
    (x0 * star x1).im = (x1 * star x2).im ∧ (x1 * star x2).im = (x2 * star x0).im := by
  have h2 : x2 = -x0 - x1 := by linear_combination h
  subst h2
  simp only [Complex.star_def, map_sub, map_neg, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.neg_re, Complex.neg_im, Complex.conj_re, Complex.conj_im]
  constructor <;> ring

theorem lipari_row_sum (U : Matrix (Fin 3) (Fin 3) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin 3) ℂ)
    (α β : Fin 3) (h : α ≠ β) :
    U α 0 * star (U β 0) + U α 1 * star (U β 1) + U α 2 * star (U β 2) = 0 := by
  have h1 := congrFun (congrFun (Matrix.mem_unitaryGroup_iff.mp hU) α) β
  rw [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply_ne h] at h1
  simp only [Matrix.star_apply] at h1
  exact h1

theorem lipari_J_row {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) (α β j k : Fin n) :
    LipariNeutrino.jarlskogCoeff U α β j k =
      -((U α j * star (U β j)) * star (U α k * star (U β k))).im := by
  unfold LipariNeutrino.jarlskogCoeff
  rw [star_mul', star_star, show U α j * star (U α k) * star (U β j) * U β k =
    U α j * star (U β j) * (star (U α k) * U β k) by ring]

theorem lipari_mass_cyclic (U : Matrix (Fin 3) (Fin 3) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin 3) ℂ) (α β : Fin 3) :
    LipariNeutrino.jarlskogCoeff U α β 0 1 = LipariNeutrino.jarlskogCoeff U α β 1 2 ∧
    LipariNeutrino.jarlskogCoeff U α β 1 2 = LipariNeutrino.jarlskogCoeff U α β 2 0 := by
  by_cases h : α = β
  · subst h
    simp only [LipariNeutrino.jarlskogCoeff, Complex.star_def, Complex.mul_im, Complex.mul_re,
      Complex.conj_re, Complex.conj_im]
    constructor <;> ring
  · rw [lipari_J_row, lipari_J_row, lipari_J_row]
    obtain ⟨h1, h2⟩ := lipari_im_cyclic _ _ _ (lipari_row_sum U hU α β h)
    exact ⟨by rw [h1], by rw [h2]⟩

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

theorem lipari_trig (a b : ℝ) :
    Real.sin (2 * a) + Real.sin (2 * b) - Real.sin (2 * (a + b)) =
      4 * Real.sin a * Real.sin b * Real.sin (a + b) := by
  rw [Real.sin_two_mul, Real.sin_two_mul, Real.sin_two_mul, Real.cos_add, Real.sin_add]
  linear_combination (-2 * Real.sin a * Real.cos a) * Real.sin_sq_add_cos_sq b +
    (-2 * Real.sin b * Real.cos b) * Real.sin_sq_add_cos_sq a

theorem lipari_normSq_sum (z0 z1 z2 : ℂ) (h : z0 + z1 + z2 = 0) :
    Complex.normSq z0 + Complex.normSq z1 + Complex.normSq z2 +
      2 * ((star z0 * z1).re + (star z0 * z2).re + (star z1 * z2).re) = 0 := by
  have h2 : z2 = -z0 - z1 := by linear_combination h
  subst h2
  simp only [Complex.normSq_apply, Complex.star_def, Complex.mul_re,
    Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im, Complex.conj_re,
    Complex.conj_im]
  ring

theorem lipari_amp_eq {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) (α β j k : Fin n) :
    LipariNeutrino.ampCoeff U α β j k =
      -4 * (star (U β j * star (U α j)) * (U β k * star (U α k))).re := by
  unfold LipariNeutrino.ampCoeff
  rw [star_mul', star_star, show U α j * star (U β j) * star (U α k) * U β k =
    star (U β j) * U α j * (U β k * star (U α k)) by ring]

theorem lipari_J_amp {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) (α β j k : Fin n) :
    LipariNeutrino.jarlskogCoeff U α β j k =
      -(star (U β j * star (U α j)) * (U β k * star (U α k))).im := by
  unfold LipariNeutrino.jarlskogCoeff
  rw [star_mul', star_star, show U α j * star (U α k) * star (U β j) * U β k =
    star (U β j) * U α j * (U β k * star (U α k)) by ring]

open LipariNeutrino in
theorem solution (U : Matrix (Fin 3) (Fin 3) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin 3) ℂ) (m2 : Fin 3 → ℝ) (L E : ℝ)
    (α β : Fin 3) (hαβ : α ≠ β) :
    oscProb U m2 L E α β =
      ampCoeff U α β 0 1 * Real.sin ((m2 1 - m2 0) * L / (4 * E)) ^ 2 +
      ampCoeff U α β 1 2 * Real.sin ((m2 2 - m2 1) * L / (4 * E)) ^ 2 +
      ampCoeff U α β 0 2 * Real.sin ((m2 2 - m2 0) * L / (4 * E)) ^ 2 -
      8 * jarlskogCoeff U α β 0 1 *
        Real.sin ((m2 1 - m2 0) * L / (4 * E)) *
        Real.sin ((m2 2 - m2 1) * L / (4 * E)) *
        Real.sin ((m2 2 - m2 0) * L / (4 * E)) := by
  obtain ⟨hc1, hc2⟩ := lipari_mass_cyclic U hU α β
  have hN := lipari_normSq_sum _ _ _ (lipari_row_sum U hU β α (Ne.symm hαβ))
  have hA01 := lipari_amp_eq U α β 0 1
  have hA12 := lipari_amp_eq U α β 1 2
  have hA02 := lipari_amp_eq U α β 0 2
  have hJ01 := lipari_J_amp U α β 0 1
  have hJ12 := lipari_J_amp U α β 1 2
  have hJ20 : jarlskogCoeff U α β 2 0 =
      (star (U β 0 * star (U α 0)) * (U β 2 * star (U α 2))).im := by
    rw [lipari_J_amp]
    simp only [Complex.star_def, map_mul, Complex.conj_conj, Complex.mul_im, Complex.mul_re,
      Complex.conj_re, Complex.conj_im]
    ring
  have e1 : m2 1 * L / (2 * E) - m2 0 * L / (2 * E) = 2 * ((m2 1 - m2 0) * L / (4 * E)) := by
    ring
  have e2 : m2 2 * L / (2 * E) - m2 0 * L / (2 * E) =
      2 * ((m2 1 - m2 0) * L / (4 * E) + (m2 2 - m2 1) * L / (4 * E)) := by ring
  have e3 : m2 2 * L / (2 * E) - m2 1 * L / (2 * E) = 2 * ((m2 2 - m2 1) * L / (4 * E)) := by
    ring
  have e4 : (m2 2 - m2 0) * L / (4 * E) =
      (m2 1 - m2 0) * L / (4 * E) + (m2 2 - m2 1) * L / (4 * E) := by ring
  unfold oscProb oscAmp
  rw [Fin.sum_univ_three, lipari_expand3, e1, e2, e3, e4]
  have hC2a := Real.cos_two_mul_eq_one_sub ((m2 1 - m2 0) * L / (4 * E))
  have hC2b := Real.cos_two_mul_eq_one_sub ((m2 2 - m2 1) * L / (4 * E))
  have hC2ab := Real.cos_two_mul_eq_one_sub
    ((m2 1 - m2 0) * L / (4 * E) + (m2 2 - m2 1) * L / (4 * E))
  have htrig := lipari_trig ((m2 1 - m2 0) * L / (4 * E)) ((m2 2 - m2 1) * L / (4 * E))
  set a := (m2 1 - m2 0) * L / (4 * E) with ha
  set b := (m2 2 - m2 1) * L / (4 * E) with hb
  set z0 := U β 0 * star (U α 0) with hz0
  set z1 := U β 1 * star (U α 1) with hz1
  set z2 := U β 2 * star (U α 2) with hz2
  linear_combination hN + 2 * (star z0 * z1).re * hC2a + 2 * (star z1 * z2).re * hC2b +
    2 * (star z0 * z2).re * hC2ab - Real.sin a ^ 2 * hA01 - Real.sin b ^ 2 * hA12 -
    Real.sin (a + b) ^ 2 * hA02 + 2 * Real.sin (2 * a) * hJ01 + 2 * Real.sin (2 * b) * hJ12 -
    2 * Real.sin (2 * (a + b)) * hJ20 +
    (2 * Real.sin (2 * b) - 2 * Real.sin (2 * (a + b))) * hc1 -
    2 * Real.sin (2 * (a + b)) * hc2 - 2 * jarlskogCoeff U α β 0 1 * htrig
