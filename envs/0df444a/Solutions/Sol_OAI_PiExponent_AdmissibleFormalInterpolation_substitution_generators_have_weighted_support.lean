-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.substitution_generators_have_weighted_support
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T17:17:45.988176+00:00
-- url     : https://prove2.me/submissions/c37ccd53-3264-4cc2-b51c-f4f2e9b735b7

import Mathlib
import Definitions.Def_OAI_PiExponent_WeightedJetShear

open OAI.PiExponent OAI.PiExponent.AdmissibleFormalInterpolation
open scoped BigOperators
theorem solution
    {m : ℕ} (v0 : ℝ) (u : Fin m → ℝ)
    (L : Fin m → MvPowerSeries (Fin (m + 1)) ℂ)
    (hL : ∀ i α,
      (∑ j, Fin.cases v0 u j * (α j : ℝ)) < u i →
        MvPowerSeries.coeff α (L i) = 0) :
    ∀ (i : Fin (m + 1)) (α : Fin (m + 1) →₀ ℕ),
      (∑ j, Fin.cases v0 u j * (α j : ℝ)) < Fin.cases v0 u i →
        MvPowerSeries.coeff α
          (Fin.cases (MvPowerSeries.X 0)
            (fun i => MvPowerSeries.X i.succ + L i) i) = 0 := by
  classical
  intro i α hα
  have hsingle : ∀ k : Fin (m + 1), α = Finsupp.single k 1 →
      (∑ j, Fin.cases v0 u j * (α j : ℝ)) = Fin.cases v0 u k := by
    intro k hk
    subst hk
    rw [Finset.sum_eq_single k]
    · simp
    · intro j _ hj; simp [Ne.symm hj]
    · simp
  induction i using Fin.cases with
  | zero =>
    simp only [Fin.cases_zero, MvPowerSeries.coeff_X]
    split_ifs with h
    · have := hsingle 0 h
      simp only [Fin.cases_zero] at hα this
      linarith
    · rfl
  | succ k =>
    simp only [Fin.cases_succ] at hα ⊢
    rw [map_add, MvPowerSeries.coeff_X, hL k α hα, add_zero]
    split_ifs with h
    · have := hsingle k.succ h
      simp only [Fin.cases_succ] at this
      linarith
    · rfl
