-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.monomial_shear_factor_power_support_of_factor_support
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T17:17:52.962248+00:00
-- url     : https://prove2.me/submissions/9d4027f7-d217-452a-8e1e-803edf3cc5b5

import Mathlib
import Definitions.Def_OAI_PiExponent_FormalJetShear

open scoped BigOperators
theorem solution
    {m : ℕ} (i : Fin m) (n : ℕ)
    (f : MvPowerSeries (Fin (m + 1)) ℂ)
    (hf : ∀ e : Fin (m + 1) →₀ ℕ,
      MvPowerSeries.coeff e f ≠ 0 →
        e i.succ ≤ 1 ∧ ∀ j : Fin m, j ≠ i → e j.succ = 0)
    (d : Fin (m + 1) →₀ ℕ) :
    (MvPowerSeries.coeff d (f ^ n) ≠ 0 → d i.succ ≤ n) ∧
    (∀ j : Fin m, j ≠ i → d j.succ ≠ 0 →
      MvPowerSeries.coeff d (f ^ n) = 0) := by
  have key : ∀ n : ℕ, ∀ e : Fin (m + 1) →₀ ℕ, MvPowerSeries.coeff e (f ^ n) ≠ 0 →
      e i.succ ≤ n ∧ ∀ j : Fin m, j ≠ i → e j.succ = 0 := by
    intro n
    induction n with
    | zero =>
      intro e he
      rw [pow_zero, MvPowerSeries.coeff_one] at he
      split_ifs at he with h
      · subst h; simp
      · exact absurd rfl he
    | succ n ih =>
      intro e he
      rw [pow_succ, MvPowerSeries.coeff_mul] at he
      obtain ⟨x, hx, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero he
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
      obtain ⟨h1, h1'⟩ := ih x.1 (left_ne_zero_of_mul hne)
      obtain ⟨h2, h2'⟩ := hf x.2 (right_ne_zero_of_mul hne)
      subst hx
      refine ⟨by simp only [Finsupp.add_apply]; omega, fun j hj => ?_⟩
      simp [h1' j hj, h2' j hj]
  refine ⟨fun h => (key n d h).1, fun j hj hd => ?_⟩
  by_contra h
  exact hd ((key n d h).2 j hj)
