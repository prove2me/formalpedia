-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.explicitCenteredExpression_firstJet
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-15T06:32:15.403766+00:00
-- url     : https://prove2.me/submissions/d02fc4ad-6a93-4459-98e6-25c5296a1da4

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.PowerSeries.Log

open OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution {m : Nat} :
    (∀ i : Fin (m + 1), MvPowerSeries.coeff 0
      (if i = 0 then MvPowerSeries.X 0 else
        MvPowerSeries.X i + liftLogSeries m (PowerSeries.log Complex) - MvPowerSeries.X 0) = 0) ∧
    (∀ i j : Fin (m + 1), MvPowerSeries.coeff (Finsupp.single j 1)
      (if i = 0 then MvPowerSeries.X 0 else
        MvPowerSeries.X i + liftLogSeries m (PowerSeries.log Complex) - MvPowerSeries.X 0) =
        (if i = j then 1 else 0)) := by
  classical
  have heq :
      MvPowerSeries.finSuccEquiv ℂ m (liftLogSeries m (PowerSeries.log ℂ)) =
        PowerSeries.map (MvPowerSeries.C : ℂ →+* MvPowerSeries (Fin m) ℂ)
          (PowerSeries.log ℂ) := by
    change (MvPowerSeries.finSuccEquiv ℂ m)
      ((MvPowerSeries.finSuccEquiv ℂ m).symm
        (PowerSeries.map MvPowerSeries.C (PowerSeries.log ℂ))) = _
    exact (MvPowerSeries.finSuccEquiv ℂ m).apply_symm_apply _
  have hcoeff (k : ℕ) (x : Fin m →₀ ℕ) :
      MvPowerSeries.coeff (Finsupp.cons k x)
          (liftLogSeries m (PowerSeries.log ℂ)) =
        MvPowerSeries.coeff x (MvPowerSeries.C
          (PowerSeries.coeff k (PowerSeries.log ℂ))) := by
    rw [← MvPowerSeries.coeff_coeff_finSuccEquiv, heq, PowerSeries.coeff_map]
  have hconst :
      MvPowerSeries.constantCoeff (liftLogSeries m (PowerSeries.log ℂ)) = 0 := by
    simpa [PowerSeries.coeff_log, MvPowerSeries.coeff_zero_C] using hcoeff 0 0
  have hlinear (j : Fin (m + 1)) :
      MvPowerSeries.coeff (Finsupp.single j 1)
        (liftLogSeries m (PowerSeries.log ℂ)) = (if j = 0 then 1 else 0) := by
    cases j using Fin.cases with
    | zero =>
        simpa [Finsupp.cons_zero_eq_single_zero,
          MvPowerSeries.coeff_zero_C, PowerSeries.coeff_one_log] using hcoeff 1 0
    | succ j =>
        simpa [Finsupp.cons_zero_single_eq_single_succ,
          PowerSeries.coeff_log] using hcoeff 0 (Finsupp.single j 1)
  constructor
  · intro i
    by_cases hi : i = 0
    · simp [hi]
    · simp [hi, hconst]
  · intro i j
    by_cases hi : i = 0
    · simp [hi, MvPowerSeries.coeff_index_single_X, eq_comm]
    · simp [hi, hlinear, MvPowerSeries.coeff_index_single_X, eq_comm]