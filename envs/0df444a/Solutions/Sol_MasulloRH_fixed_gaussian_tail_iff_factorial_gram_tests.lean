-- Prove2me | solution 1 for MasulloRH.fixed_gaussian_tail_iff_factorial_gram_tests
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T22:28:11.484803+00:00
-- url     : https://prove2.me/submissions/014eea61-68f8-4286-9a87-cebba3a3d927

import Theorems.Thm_MasulloRH_unit_gaussian_approximation_iff_shifted_gram_indefinite
import Theorems.Thm_MasulloRH_expanding_gaussian_window_energy_monotone
import Theorems.Thm_MasulloRH_factorial_grid_realizes_finite_rational_theta_sums
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open MasulloRH MasulloRH.FixedGaussianTest MasulloRH.GaussianApproximation MasulloRH.RationalThetaGrid

private lemma edges (k : ℕ) : 0 < fullCenter k-fullWidth k ∧ fullCenter k+fullWidth k < 1 := by
  have el : fullCenter k-fullWidth k = left k := by unfold fullCenter fullWidth;ring
  have er : fullCenter k+fullWidth k = upper k := by unfold fullCenter fullWidth;ring
  rw [el,er]
  exact ⟨by unfold left;positivity,max_lt (by norm_num [right]) (sub_lt_self _ (by positivity))⟩

theorem solution : tailApprox ↔ ∀ j : ℕ, 16384 ≤ j → ∃ n : ℕ, passes j n := by
  constructor
  · intro h j hj
    obtain ⟨k,hk,m,a,y,he⟩ := h j hj
    have hs := (expanding_gaussian_window_energy_monotone _ _ hk).trans_lt he
    obtain ⟨n,hn⟩ := factorial_grid_realizes_finite_rational_theta_sums.1 m y
    obtain ⟨b,hb⟩ := factorial_grid_realizes_finite_rational_theta_sums.2 a y (mesh n) (hn n le_rfl)
    rw [hb] at hs
    exact ⟨n,(unit_gaussian_approximation_iff_shifted_gram_indefinite _ _ _ (edges _).1 (edges _).2 _ _).1 ⟨b,hs⟩⟩
  · intro h j hj
    obtain ⟨n,hn⟩ := h j hj
    obtain ⟨b,hb⟩ := (unit_gaussian_approximation_iff_shifted_gram_indefinite _ _ _ (edges _).1 (edges _).2 _ _).2 hn
    exact ⟨j+1,le_rfl,gridCount n,b,mesh n,hb⟩
