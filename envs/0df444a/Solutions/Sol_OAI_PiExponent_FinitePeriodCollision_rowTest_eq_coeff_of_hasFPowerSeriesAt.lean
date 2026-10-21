-- Prove2me | solution 1 for OAI.PiExponent.FinitePeriodCollision.rowTest_eq_coeff_of_hasFPowerSeriesAt
-- status  : ACCEPTED   (prove)
-- author  : @polylog
-- created : 2026-10-20T18:38:31.010597+00:00
-- url     : https://prove2.me/submissions/9b644f67-986b-4321-8cdb-db5f439066a4

import Definitions.Def_OAI_PiExponent_FinitePeriodAnalytic
import Mathlib.Analysis.Complex.CauchyIntegral

open scoped NNReal
open OAI.PiExponent.FinitePeriodCollision

/-- The Cauchy row test extracts the corresponding coefficient of any formal power series that
represents `f` at the origin, provided `f` is complex differentiable on the closed disc of
radius `1/2`. -/
theorem solution (ell : ℕ) (f : ℂ → ℂ) (s : PowerSeries ℂ)
    (hd : DifferentiableOn ℂ f (Metric.closedBall 0 (1 / 2)))
    (hp : HasFPowerSeriesAt f
      (FormalMultilinearSeries.ofScalars ℂ
        (fun n => PowerSeries.coeff n s)) 0) :
    rowTest ell f = PowerSeries.coeff ell s := by
  have hball := hd.hasFPowerSeriesOnBall (R := (1 / 2 : ℝ≥0)) (by norm_num)
  have heq := hball.hasFPowerSeriesAt.eq_formalMultilinearSeries hp
  have hh := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p ell (fun _ => 1)) heq
  simpa only [rowTest, FormalMultilinearSeries.apply_eq_prod_smul_coeff,
    Finset.prod_const_one, one_smul, FormalMultilinearSeries.coeff_ofScalars,
    NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] using hh
