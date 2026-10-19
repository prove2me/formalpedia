-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.FiniteTranslation.logMajorant_power_coeff_eq_composition_sum_generic
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T18:35:16.313564+00:00
-- url     : https://prove2.me/submissions/b07f6ed1-c052-45cf-a757-7db8dc8d9bcb

import Definitions.Def_OAI_PiExponent_FiniteActualTranslation
import Definitions.Def_OAI_PiExponent_logMajorantCompositions
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_coeff_pow_eq_bounded_fin_tuple_sum_generic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_bounded_sum_eq_logMajorant_composition_sum_generic

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem solution (q k : ℕ) (f : ℕ → ℂ) (h0 : f 0 = 0) :
    PowerSeries.coeff k ((PowerSeries.mk f) ^ q) =
      ∑ a ∈ logMajorantCompositions q k, ∏ i : Fin q, f (a i) := by
  calc
    PowerSeries.coeff k ((PowerSeries.mk f) ^ q) =
        ∑ a ∈ (Finset.univ : Finset (Fin q → Fin (k + 1))).filter
          (fun a => (∑ i : Fin q, (a i : ℕ)) = k), ∏ i : Fin q, f (a i) :=
      OAI.PiExponent.DeterminantContradiction.FiniteTranslation.coeff_pow_eq_bounded_fin_tuple_sum_generic
        q k f
    _ = ∑ a ∈ logMajorantCompositions q k, ∏ i : Fin q, f (a i) :=
      OAI.PiExponent.DeterminantContradiction.FiniteTranslation.bounded_sum_eq_logMajorant_composition_sum_generic
        q k f h0