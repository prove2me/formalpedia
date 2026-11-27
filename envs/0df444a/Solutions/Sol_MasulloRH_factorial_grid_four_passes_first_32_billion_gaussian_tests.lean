-- Prove2me | solution 1 for MasulloRH.factorial_grid_four_passes_first_32_billion_gaussian_tests
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-27T00:16:34.949722+00:00
-- url     : https://prove2.me/submissions/b1ed6d10-2d87-4fc4-aaa9-8f4ee108d8c4

import Theorems.Thm_MasulloRH_twenty_five_rational_translates_gaussian_all_windows
import Theorems.Thm_MasulloRH_unit_gaussian_approximation_iff_shifted_gram_indefinite
import Theorems.Thm_MasulloRH_factorial_grid_realizes_finite_rational_theta_sums
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open MasulloRH MasulloRH.FixedGaussianTest MasulloRH.GaussianApproximation MasulloRH.RationalThetaGrid

theorem solution (j : ℕ) (hj : j < 32000000000) : passes j 4 := by
  have cover : ∀ i : Fin 25, ∃ p : Fin (gridCount 4), mesh 4 p = ThetaDerivativeCertificate.shift i := by decide +kernel
  let a (i : Fin 25) : ℚ × ℚ := (ThetaDerivativeCertificate.coeff i,0)
  obtain ⟨b,he⟩ := factorial_grid_realizes_finite_rational_theta_sums.2 a ThetaDerivativeCertificate.shift (mesh 4) cover
  have eqc (i : Fin 25) : asComplex (a i) = (ThetaDerivativeCertificate.coeff i : ℂ) := by simp [asComplex,a]
  simp_rw [eqc] at he
  let k := j+1
  have bound := MasulloRH.twenty_five_rational_translates_gaussian_all_windows.2 k
  change energy _ _ (residual 0 _ _) < _ at bound
  rw [he] at bound
  have lo : 0 < fullCenter k-fullWidth k := by
    rw [show fullCenter k-fullWidth k=left k by unfold fullCenter fullWidth;ring];unfold left;positivity
  have hi : fullCenter k+fullWidth k < 1 := by
    rw [show fullCenter k+fullWidth k=upper k by unfold fullCenter fullWidth;ring]
    exact max_lt (by norm_num [right]) (sub_lt_self _ (by positivity))
  apply (unit_gaussian_approximation_iff_shifted_gram_indefinite _ _ _ lo hi _ _).1
  have hj' : (j:ℝ)+1 ≤ 32000000000 := by exact_mod_cast (show j+1 ≤ 32000000000 by omega)
  exact ⟨b,bound.trans_le (one_div_le_one_div_of_le (by positivity) hj')⟩
