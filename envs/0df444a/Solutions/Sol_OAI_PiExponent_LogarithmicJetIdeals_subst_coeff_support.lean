-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.subst_coeff_support
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T16:12:34.687031+00:00
-- url     : https://prove2.me/submissions/af61ce05-df7b-4298-b59a-ce3101ec6ae2

import Mathlib
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPowerSeries.Substitution
open scoped BigOperators
theorem solution
    {m : ℕ} (sigma : Fin (m + 1) → MvPowerSeries (Fin (m + 1)) ℂ)
    (hsigma : MvPowerSeries.HasSubst sigma)
    (F : MvPowerSeries (Fin (m + 1)) ℂ)
    (e : Fin (m + 1) →₀ ℕ)
    (h : MvPowerSeries.coeff e (MvPowerSeries.subst sigma F) ≠ 0) :
    ∃ d : Fin (m + 1) →₀ ℕ,
      MvPowerSeries.coeff d F ≠ 0 ∧
      MvPowerSeries.coeff e (d.prod fun i n => sigma i ^ n) ≠ 0 := by
  rw [MvPowerSeries.coeff_subst hsigma] at h
  by_contra hc
  push Not at hc
  apply h
  rw [finsum_eq_zero_of_forall_eq_zero]
  intro d
  by_cases hd : MvPowerSeries.coeff d F = 0
  · simp [hd]
  · rw [hc d hd, smul_zero]
