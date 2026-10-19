-- Prove2me | solution 1 for OAI.PiExponent.MatrixTranslationBounds.coeff_prod_finsupp_antidiag
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T17:40:28.448936+00:00
-- url     : https://prove2.me/submissions/b20fec61-2e66-4684-a828-e98e0d74b0a3

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.RingTheory.PowerSeries.Log

open scoped BigOperators

theorem solution
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : ι → PowerSeries ℂ) (k : ℕ) :
    PowerSeries.coeff k (∏ i, g i) =
      ∑ l ∈ Finset.finsuppAntidiag (Finset.univ : Finset ι) k,
        ∏ i, PowerSeries.coeff (l i) (g i) := by
  exact PowerSeries.coeff_prod g k (Finset.univ : Finset ι)