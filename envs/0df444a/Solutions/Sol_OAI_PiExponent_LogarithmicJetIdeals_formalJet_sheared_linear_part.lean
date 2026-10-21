-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.formalJet_sheared_linear_part
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-20T17:36:08.20199+00:00
-- url     : https://prove2.me/submissions/d3c414b6-db0b-4707-bd51-d8a13766775c

import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_liftLogSeries_linear_coeff

open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution {m : Nat} :
    ∀ (i : Fin (m + 1)) (d : Fin (m + 1) -> Nat),
      (∑ k : Fin (m + 1), d k) <= 1 ->
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm d)
          (Fin.cases (MvPowerSeries.X 0)
            (fun j => MvPowerSeries.X j.succ +
              liftLogSeries m (PowerSeries.log ℂ) - MvPowerSeries.X 0) i) =
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm d)
          (MvPowerSeries.X i) := by
  intro i d hd
  have hlog := OAI.PiExponent.LogarithmicJetIdeals.liftLogSeries_linear_coeff
    (m := m) d hd
  cases i using Fin.cases with
  | zero => simp
  | succ j => simp [hlog]