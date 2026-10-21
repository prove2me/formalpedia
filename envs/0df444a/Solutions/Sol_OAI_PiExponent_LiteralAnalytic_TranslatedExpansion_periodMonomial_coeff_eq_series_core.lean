-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.periodMonomial_coeff_eq_series_core
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-20T12:58:32.206385+00:00
-- url     : https://prove2.me/submissions/e5bd2f0d-9d6f-4b9b-8bc8-9a3654c9e7ca

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_TranslatedExpansion_CollisionAnalyticHelpers
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_TranslatedExpansionTerms
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_TranslatedExpansion_mvPolynomial_diagonal_binomial_coeff

open scoped BigOperators Topology
open OAI.PiExponent.LiteralAnalytic.TranslatedExpansion
open OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.CollisionAnalytic

theorem solution
    {m : ℕ} (j h : ℕ) (a : Fin m → ℕ) (A : Fin m →₀ ℕ) :
    (periodMonomial j h a).coeff A =
      PowerSeries.C ((∏ i, (a i).choose (A i) : ℕ) : ℂ) *
        (1 + PowerSeries.X) ^ h *
        (PowerSeries.C ((j : ℂ) *
          OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.period) +
          PowerSeries.log ℂ) ^
          (∑ i : Fin m, (a i - A i)) := by
  rw [periodMonomial, mvPolynomial_diagonal_binomial_coeff]
  ring