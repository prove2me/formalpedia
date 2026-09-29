-- Prove2me | solution 1 for LipariNeutrino.jarlskogCoeff_mass_cyclic
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-25T08:31:04.422997+00:00
-- url     : https://prove2.me/submissions/0fcbaca1-f133-4710-90d9-23f96a631f7a

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

open LipariNeutrino in
theorem solution (U : Matrix (Fin 3) (Fin 3) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin 3) ℂ) (α β : Fin 3) :
    jarlskogCoeff U α β 0 1 = jarlskogCoeff U α β 1 2 ∧
    jarlskogCoeff U α β 1 2 = jarlskogCoeff U α β 2 0 := by
  by_cases h : α = β
  · subst h
    simp only [LipariNeutrino.jarlskogCoeff, Complex.star_def, Complex.mul_im, Complex.mul_re,
      Complex.conj_re, Complex.conj_im]
    constructor <;> ring
  · rw [lipari_J_row, lipari_J_row, lipari_J_row]
    obtain ⟨h1, h2⟩ := lipari_im_cyclic _ _ _ (lipari_row_sum U hU α β h)
    exact ⟨by rw [h1], by rw [h2]⟩
