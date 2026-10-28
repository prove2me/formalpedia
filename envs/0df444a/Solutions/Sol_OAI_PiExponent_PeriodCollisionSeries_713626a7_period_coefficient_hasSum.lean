-- Prove2me | solution 1 for OAI.PiExponent.PeriodCollisionSeries_713626a7.period_coefficient_hasSum
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-24T19:02:08.050596+00:00
-- url     : https://prove2.me/submissions/5af69f0b-bd73-49f5-bf13-4017fc62de2d

import Definitions.Def_PiExponent_PeriodCollisionSeries_713626a7
import Theorems.Thm_OAI_PiExponent_PeriodCollisionSeries_713626a7_cauchy_composition_hasSum
import Theorems.Thm_OAI_PiExponent_PeriodCollisionSeries_713626a7_periodMonomial_coeff_eq_cauchy

open OAI.PiExponent
open OAI.PiExponent.FiniteMinorAnalysis_690acb6f
open OAI.PiExponent.PeriodCollisionSeries_713626a7
open scoped BigOperators

theorem solution
    {m : ℕ} (R : ℝ) (j h ell : ℕ) (a : Fin m → ℕ)
    (A : Fin m →₀ ℕ) (hR : 0 < R)
    (hc : ‖(j : ℂ) * period‖ + 3 / 4 ≤ R / 2) :
    HasSum (fun d : ℕ => rowFactor R j ell d * columnFactor R h a A d)
      (PowerSeries.coeff ell ((periodMonomial j h a).coeff A)) := by
  rw [periodMonomial_coeff_eq_cauchy]
  simpa only [rowFactor, columnFactor] using
    cauchy_composition_hasSum
      (f := columnFunction h a A)
      (by
        unfold columnFunction
        fun_prop)
      R hR ((j : ℂ) * period) hc ell