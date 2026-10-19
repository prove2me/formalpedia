-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.formalShear_successor_product_coeff_eq
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T17:40:25.781881+00:00
-- url     : https://prove2.me/submissions/c0b52e47-9fe9-42a9-aa81-baf4c443d587

import Definitions.Def_OAI_PiExponent_FormalJetShear
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_formalShear_successor_product_top_coeff

open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution
    {m : ℕ} (delta : Fin m → PowerSeries ℂ) (e a : Fin (m + 1) →₀ ℕ)
    (htop : ∀ i : Fin m, a i.succ = e i.succ) :
    MvPowerSeries.coeff e
        ((MvPowerSeries.X 0) ^ (a 0) *
          ∏ i : Fin m,
            (MvPowerSeries.X i.succ + liftLogSeries m (delta i)) ^ (a i.succ)) =
      PowerSeries.coeff (e 0) ((PowerSeries.X : PowerSeries ℂ) ^ (a 0)) := by
  classical
  rw [MvPowerSeries.X_pow_eq, MvPowerSeries.coeff_monomial_mul]
  by_cases hle : a 0 ≤ e 0
  · have hs : Finsupp.single (0 : Fin (m + 1)) (a 0) ≤ e := by
      intro j
      by_cases hj : j = 0
      · subst j
        simpa using hle
      · simp [hj]
    rw [if_pos hs]
    have htop' : ∀ i : Fin m,
        (e - Finsupp.single (0 : Fin (m + 1)) (a 0)) i.succ = a i.succ := by
      intro i
      simp [htop i]
    rw [OAI.PiExponent.AdmissibleFormalInterpolation.formalShear_successor_product_top_coeff
      delta a (e - Finsupp.single (0 : Fin (m + 1)) (a 0)) htop']
    by_cases heq : e 0 = a 0
    · simp [PowerSeries.coeff_X_pow, heq]
    · have hsub : e 0 - a 0 ≠ 0 := by omega
      simp [PowerSeries.coeff_X_pow, heq, hsub]
  · rw [if_neg]
    · have hne : e 0 ≠ a 0 := by omega
      simp [PowerSeries.coeff_X_pow, hne]
    · intro hs
      apply hle
      simpa using hs