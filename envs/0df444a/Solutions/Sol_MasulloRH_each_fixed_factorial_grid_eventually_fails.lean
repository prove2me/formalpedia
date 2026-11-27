-- Prove2me | solution 1 for MasulloRH.each_fixed_factorial_grid_eventually_fails
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T22:33:42.03194+00:00
-- url     : https://prove2.me/submissions/c2de443f-d8aa-4a3f-8d2f-d37011839323

import Theorems.Thm_MasulloRH_small_gaussian_error_requires_unbounded_shift_denominators
import Theorems.Thm_MasulloRH_unit_gaussian_approximation_iff_shifted_gram_indefinite
import Mathlib.Tactic.Positivity

open MasulloRH MasulloRH.RationalThetaGrid MasulloRH.GaussianApproximation MasulloRH.FixedGaussianTest

theorem solution (N : ℕ) : ∃ J : ℕ, ∀ j : ℕ, J ≤ j → ∀ n : ℕ, n ≤ N → ¬ passes j n := by
  let denBound (n : ℕ) := ∑ i : Fin (gridCount n), (mesh n i).den
  let D := ∑ h ∈ Finset.range (N+1), denBound h
  obtain ⟨J,hJ⟩ := small_gaussian_error_requires_unbounded_shift_denominators D
  refine ⟨J,?_⟩
  intro j hj n hn hp
  let k := j+1
  have lo : 0 < fullCenter k-fullWidth k := by
    rw [show fullCenter k-fullWidth k = left k by unfold fullCenter fullWidth;ring];unfold left;positivity
  have hi : fullCenter k+fullWidth k < 1 := by
    rw [show fullCenter k+fullWidth k = upper k by unfold fullCenter fullWidth;ring]
    exact max_lt (by norm_num [right]) (sub_lt_self _ (by positivity))
  obtain ⟨a,ha⟩ := (unit_gaussian_approximation_iff_shifted_gram_indefinite _ _ _ lo hi _ _).2 hp
  obtain ⟨i,hd⟩ := hJ j hj k (gridCount n) (fun i => asComplex (a i)) (mesh n) ha
  have one : (mesh n i).den ≤ denBound n :=
    Finset.single_le_sum (f:=fun i => (mesh n i).den) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have allB : denBound n ≤ D :=
    Finset.single_le_sum (f:=denBound) (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))
  exact hd.not_ge (one.trans allB)
