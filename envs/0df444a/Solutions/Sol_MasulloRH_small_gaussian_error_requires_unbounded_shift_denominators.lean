-- Prove2me | solution 1 for MasulloRH.small_gaussian_error_requires_unbounded_shift_denominators
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T22:32:39.402225+00:00
-- url     : https://prove2.me/submissions/6cd8cdf3-68d6-4455-8469-406514b3ece9

import Theorems.Thm_MasulloRH_fixed_lattice_theta_gaussian_energy_gap
import Theorems.Thm_MasulloRH_expanding_gaussian_window_energy_monotone
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open MasulloRH.RationalThetaGrid MasulloRH.GaussianApproximation MasulloRH.FixedGaussianTest

private lemma lattice_point (D : ℕ) (q : ℚ) (hq : q.den ≤ D) :
    ∃ k : ℤ, (q:ℝ) = 0 + (1/(D.factorial:ℝ))*(k:ℝ) := by
  obtain ⟨t,ht⟩ := Nat.dvd_factorial q.den_pos hq
  refine ⟨q.num*(t:ℤ),?_⟩
  have hn : (D.factorial:ℝ) ≠ 0 := by positivity
  have hd : (q.den:ℝ) ≠ 0 := by exact_mod_cast q.den_pos.ne'
  have en : (D.factorial:ℝ) = (q.den:ℝ)*(t:ℝ) := by exact_mod_cast ht
  have den : (q.num:ℝ)/(q.den:ℝ) = q := by exact_mod_cast Rat.num_div_den q
  push_cast
  rw [← den,zero_add,one_div,inv_mul_eq_div,div_eq_div_iff hd hn,en]
  ring

theorem solution (D : ℕ) :
    ∃ J : ℕ, ∀ j : ℕ, J ≤ j → ∀ (k m : ℕ) (v : Fin m → ℂ) (y : Fin m → ℚ),
      energy (fullCenter k) (fullWidth k) (residual 0 v (fun i => (y i:ℝ))) < 1/((j:ℝ)+1) →
        ∃ i : Fin m, D < (y i).den := by
  classical
  obtain ⟨δ,hδ,floor⟩ := MasulloRH.fixed_lattice_theta_gaussian_energy_gap
    (fullCenter 0) (fullWidth 0) (1/(D.factorial:ℝ)) 0
    (by norm_num [fullCenter,fullWidth,left,upper,right]) (by norm_num [fullCenter,fullWidth,left,upper,right])
    (by norm_num [fullCenter,fullWidth,left,upper,right]) (by positivity)
  obtain ⟨J,hJ⟩ := exists_nat_gt (1/δ)
  refine ⟨J,?_⟩
  intro j hj k m v y he
  by_contra! hn
  choose u hu using fun i => lattice_point D (y i) (hn i)
  have e : (fun i => (y i:ℝ)) = (fun i => 0+(1/(D.factorial:ℝ))*(u i:ℝ)) := funext hu
  have hlo := (floor m v u).trans (MasulloRH.expanding_gaussian_window_energy_monotone v _ (Nat.zero_le k))
  rw [← e] at hlo
  have hj' : (J:ℝ) ≤ j := by exact_mod_cast hj
  have hsmall : 1/((j:ℝ)+1) < δ := by
    apply (div_lt_iff₀ (by positivity)).2
    have h := (div_lt_iff₀ hδ).1 hJ
    nlinarith [mul_nonneg (sub_nonneg.mpr hj') hδ.le]
  exact (he.trans hsmall).not_ge hlo
