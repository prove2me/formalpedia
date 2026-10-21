-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.periodMonomial_coeff_eq_series
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-20T12:34:06.419141+00:00
-- url     : https://prove2.me/submissions/719e06e5-286d-4255-8848-1fda16589505

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_TranslatedExpansion_CollisionAnalyticHelpers
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_TranslatedExpansionTerms
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_TranslatedExpansion_periodMonomial_coeff_eq_series_core

open scoped BigOperators Topology
open OAI.PiExponent.LiteralAnalytic.TranslatedExpansion
open OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.CollisionAnalytic

theorem solution
    {m : ℕ} (j h ell : ℕ) (a : Fin m → ℕ) (A : Fin m →₀ ℕ) :
    PowerSeries.coeff ell ((periodMonomial j h a).coeff A) =
    PowerSeries.coeff ell
      (PowerSeries.C ((∏ i, (a i).choose (A i) : ℕ) : ℂ) *
        (1 + PowerSeries.X) ^ h *
        (PowerSeries.C ((j : ℂ) *
          OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.period) +
          PowerSeries.log ℂ) ^
          (∑ i : Fin m, (a i - A i))) := by
  have hcoeff :=
    OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.periodMonomial_coeff_eq_series_core
      j h a A
  simpa using congrArg (PowerSeries.coeff ell) hcoeff