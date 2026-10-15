-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.polynomial_series_coordinate_change_factorization
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-14T21:58:33.223434+00:00
-- url     : https://prove2.me/submissions/4215dc26-41c1-473b-9187-b2e427010422

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_LocalCoordinatePolynomial
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_coordinate_evaluation

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open scoped BigOperators

theorem solution
    {m : ℕ} (c : Fin m → ℂ) (G : Fin m → PowerSeries ℂ)
    (H : Fin m → Polynomial ℂ) (P : MvPolynomial (Fin (m + 1)) ℂ) :
    MvPolynomial.aeval
      (Fin.cases (MvPowerSeries.X 0)
        (fun i => MvPowerSeries.X i.succ +
          liftLogSeries m (G i - (H i : PowerSeries ℂ))))
      (MvPolynomial.aeval
        (Fin.cases (1 + MvPolynomial.X 0)
          (fun i => MvPolynomial.C (c i) + MvPolynomial.X i.succ +
            Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X 0) (H i))) P) =
    MvPolynomial.aeval
      (Fin.cases (1 + MvPowerSeries.X 0)
        (fun i => MvPowerSeries.C (c i) + MvPowerSeries.X i.succ +
          liftLogSeries m (G i))) P := by
  rw [MvPolynomial.comp_aeval_apply]
  have hcoord :
      (fun i : Fin (m + 1) =>
        MvPolynomial.aeval
          (Fin.cases (MvPowerSeries.X 0)
            (fun j => MvPowerSeries.X j.succ +
              liftLogSeries m (G j - (H j : PowerSeries ℂ))))
          (Fin.cases (1 + MvPolynomial.X 0)
            (fun j => MvPolynomial.C (c j) + MvPolynomial.X j.succ +
              Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X 0) (H j)) i)) =
      Fin.cases (1 + MvPowerSeries.X 0)
        (fun i => MvPowerSeries.C (c i) + MvPowerSeries.X i.succ +
          liftLogSeries m (G i)) := by
    funext i
    exact OAI.PiExponent.LogarithmicJetIdeals.coordinate_evaluation c G H i
  exact congrArg (fun f : Fin (m + 1) → MvPowerSeries (Fin (m + 1)) ℂ =>
    MvPolynomial.aeval f P) hcoord