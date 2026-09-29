-- Prove2me | solution 1 for LipariNeutrino.jarlskog_pmns
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-25T09:02:33.078492+00:00
-- url     : https://prove2.me/submissions/054d1498-6a5e-4725-949d-39f23d5fcf53

import Mathlib
import Definitions.Def_LipariNeutrino_OscillationProbability
import Definitions.Def_LipariNeutrino_MixingMatrices

set_option autoImplicit false

theorem lipari_pmns_00 (θ12 θ13 θ23 δ : ℝ) :
    LipariNeutrino.pmns θ12 θ13 θ23 δ 0 0 = (Real.cos θ13 : ℂ) * (Real.cos θ12 : ℂ) := by
  simp [LipariNeutrino.pmns, Matrix.mul_apply, Fin.sum_univ_three]

theorem lipari_pmns_01 (θ12 θ13 θ23 δ : ℝ) :
    LipariNeutrino.pmns θ12 θ13 θ23 δ 0 1 = (Real.cos θ13 : ℂ) * (Real.sin θ12 : ℂ) := by
  simp [LipariNeutrino.pmns, Matrix.mul_apply, Fin.sum_univ_three]

theorem lipari_pmns_10 (θ12 θ13 θ23 δ : ℝ) :
    LipariNeutrino.pmns θ12 θ13 θ23 δ 1 0 = -((Real.cos θ23 : ℂ) * (Real.sin θ12 : ℂ)) -
      (Real.sin θ23 : ℂ) * (Real.sin θ13 : ℂ) * (Real.cos θ12 : ℂ) *
        Complex.exp (Complex.I * (δ : ℂ)) := by
  simp [LipariNeutrino.pmns, Matrix.mul_apply, Fin.sum_univ_three]
  ring

theorem lipari_pmns_11 (θ12 θ13 θ23 δ : ℝ) :
    LipariNeutrino.pmns θ12 θ13 θ23 δ 1 1 = (Real.cos θ23 : ℂ) * (Real.cos θ12 : ℂ) -
      (Real.sin θ23 : ℂ) * (Real.sin θ13 : ℂ) * (Real.sin θ12 : ℂ) *
        Complex.exp (Complex.I * (δ : ℂ)) := by
  simp [LipariNeutrino.pmns, Matrix.mul_apply, Fin.sum_univ_three]
  ring

theorem lipari_exp_pos (φ : ℝ) :
    Complex.exp (Complex.I * (φ : ℂ)) = (Real.cos φ : ℂ) + (Real.sin φ : ℂ) * Complex.I := by
  rw [mul_comm, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

open LipariNeutrino in
theorem solution (θ12 θ13 θ23 δ : ℝ) :
    jarlskogCoeff (pmns θ12 θ13 θ23 δ) 0 1 0 1 =
      -(Real.cos θ13 ^ 2 * Real.sin θ13 * Real.sin θ12 * Real.cos θ12 *
          Real.sin θ23 * Real.cos θ23 * Real.sin δ) := by
  unfold jarlskogCoeff
  rw [lipari_pmns_00, lipari_pmns_01, lipari_pmns_10, lipari_pmns_11, lipari_exp_pos]
  simp only [Complex.mul_im, Complex.mul_re, Complex.add_re, Complex.add_im, Complex.sub_re,
    Complex.sub_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
  linear_combination (-(Real.cos θ13 ^ 2 * Real.cos θ12 * Real.sin θ12 * Real.cos θ23 *
    Real.sin θ23 * Real.sin θ13 * Real.sin δ)) * Real.sin_sq_add_cos_sq θ12
