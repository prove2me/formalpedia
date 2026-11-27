-- Prove2me | solution 1 for MasulloRH.thirty_seven_shift_gram_passes_first_16666_tests
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T22:28:12.209262+00:00
-- url     : https://prove2.me/submissions/770071af-0aae-4bf3-ad37-8d6f2536bd14

import Theorems.Thm_MasulloRH_nine_shift_residual_central_integral
import Theorems.Thm_MasulloRH_nine_shift_residual_uniform_exterior
import Theorems.Thm_MasulloRH_unit_gaussian_approximation_iff_shifted_gram_indefinite
import Theorems.Thm_MasulloRH_factorial_grid_realizes_finite_rational_theta_sums
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open MasulloRH MasulloRH.FixedGaussianTest MasulloRH.GaussianApproximation MasulloRH.RationalThetaGrid

theorem solution (j : ℕ) (hj : j < 16666) : passes j 3 := by
  have cover : ∀ i : Fin 9, ∃ p : Fin (gridCount 3), mesh 3 p = NineShift.shift i := by decide +kernel
  let a (i : Fin 9) : ℚ × ℚ := (NineShift.coeff i,0)
  obtain ⟨b,he⟩ := factorial_grid_realizes_finite_rational_theta_sums.2 a NineShift.shift (mesh 3) cover
  have eqc (i : Fin 9) : asComplex (a i) = (NineShift.coeff i : ℂ) := by simp [asComplex,a]
  simp_rw [eqc] at he
  let k := j+1
  have hl : 1/2 ≤ fullCenter k-fullWidth k := by
    rw [show fullCenter k-fullWidth k = left k by unfold fullCenter fullWidth;ring]
    unfold left
    exact le_add_of_nonneg_right (by positivity)
  have hr : fullCenter k+fullWidth k ≤ 1 := by
    rw [show fullCenter k+fullWidth k = upper k by unfold fullCenter fullWidth;ring]
    exact max_le (by norm_num [right]) (sub_le_self _ (by positivity))
  have ext := nine_shift_residual_uniform_exterior _ _ hl hr
  have cen := nine_shift_residual_central_integral _ _ hl hr ext.1
  have bound : energy (fullCenter k) (fullWidth k) NineShift.err < 1/16666 := by linarith only [ext.2,cen]
  change energy _ _ (residual 0 _ _) < _ at bound
  rw [he] at bound
  have lo : 0 < fullCenter k-fullWidth k := by
    rw [show fullCenter k-fullWidth k=left k by unfold fullCenter fullWidth;ring];unfold left;positivity
  have hi : fullCenter k+fullWidth k < 1 := by
    rw [show fullCenter k+fullWidth k=upper k by unfold fullCenter fullWidth;ring]
    exact max_lt (by norm_num [right]) (sub_lt_self _ (by positivity))
  apply (unit_gaussian_approximation_iff_shifted_gram_indefinite _ _ _ lo hi _ _).1
  have hj' : (j:ℝ)+1 ≤ 16666 := by exact_mod_cast (show j+1 ≤ 16666 by omega)
  exact ⟨b,bound.trans_le (one_div_le_one_div_of_le (by positivity) hj')⟩
