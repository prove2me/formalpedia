-- Prove2me | solution 1 for OAI.PiExponent.FinitePeriodCollision.rowTest_periodFunction_coeff
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-20T13:09:36.880525+00:00
-- url     : https://prove2.me/submissions/ad0cfc88-2aef-407f-a396-0d5c4b608079

import Definitions.Def_OAI_PiExponent_FinitePeriodAnalytic
import Theorems.Thm_OAI_PiExponent_FinitePeriodCollision_hasFPowerSeriesAt_periodFunction
import Theorems.Thm_OAI_PiExponent_FinitePeriodCollision_rowTest_eq_coeff_of_hasFPowerSeriesAt
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

open scoped BigOperators
open OAI.PiExponent
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation
open OAI.PiExponent.FinitePeriodCollision

theorem solution
    (b center : ℂ) (h d ell : ℕ) :
    rowTest ell (fun t => b * (1 + t) ^ h *
        (center + Complex.log (1 + t)) ^ d) =
      PowerSeries.coeff ell
        (PowerSeries.C b * (1 + PowerSeries.X) ^ h *
          (PowerSeries.C center + PowerSeries.log ℂ) ^ d) := by
  have hd : DifferentiableOn ℂ
      (fun t : ℂ => b * (1 + t) ^ h * (center + Complex.log (1 + t)) ^ d)
      (Metric.closedBall 0 (1 / 2)) := by
    intro z hz
    have hz' : ‖z‖ < 1 := by
      have hz'' : ‖z‖ ≤ (1 / 2 : ℝ) := by
        simpa only [Metric.mem_closedBall, dist_zero_right] using hz
      linarith
    have ha : AnalyticAt ℂ
        (fun t : ℂ => b * (1 + t) ^ h * (center + Complex.log (1 + t)) ^ d) z := by
      apply AnalyticAt.mul
      · fun_prop
      · exact (analyticAt_const.add
          ((analyticAt_const.add analyticAt_id).clog
            (Complex.mem_slitPlane_of_norm_lt_one hz'))).pow d
    exact ha.differentiableAt.differentiableWithinAt
  exact OAI.PiExponent.FinitePeriodCollision.rowTest_eq_coeff_of_hasFPowerSeriesAt
    ell _ _ hd
    (OAI.PiExponent.FinitePeriodCollision.hasFPowerSeriesAt_periodFunction b center h d)