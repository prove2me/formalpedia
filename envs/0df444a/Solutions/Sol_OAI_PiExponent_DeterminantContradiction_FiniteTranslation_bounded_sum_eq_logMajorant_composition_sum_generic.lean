-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.FiniteTranslation.bounded_sum_eq_logMajorant_composition_sum_generic
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T18:40:47.22887+00:00
-- url     : https://prove2.me/submissions/13db1b2d-1c6f-43c9-bb3c-42cad10ca12a

import Definitions.Def_OAI_PiExponent_FiniteActualTranslation
import Definitions.Def_OAI_PiExponent_logMajorantCompositions
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_bounded_sum_eq_positive_bounded_sum_generic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_positive_bounded_sum_eq_logMajorant_composition_sum_generic

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem solution (q k : ℕ) (f : ℕ → ℂ) (h0 : f 0 = 0) :
    (∑ a ∈ (Finset.univ : Finset (Fin q → Fin (k + 1))).filter
      (fun a => (∑ i : Fin q, (a i : ℕ)) = k), ∏ i : Fin q, f (a i)) =
      ∑ a ∈ logMajorantCompositions q k, ∏ i : Fin q, f (a i) := by
  calc
    (∑ a ∈ (Finset.univ : Finset (Fin q → Fin (k + 1))).filter
        (fun a => (∑ i : Fin q, (a i : ℕ)) = k), ∏ i : Fin q, f (a i)) =
        ∑ a ∈ ((Finset.univ : Finset (Fin q → Fin (k + 1))).filter
          (fun a => (∑ i : Fin q, (a i : ℕ)) = k)).filter
            (fun a => ∀ i : Fin q, 0 < (a i : ℕ)), ∏ i : Fin q, f (a i) :=
      OAI.PiExponent.DeterminantContradiction.FiniteTranslation.bounded_sum_eq_positive_bounded_sum_generic
        q k f h0
    _ = ∑ a ∈ logMajorantCompositions q k, ∏ i : Fin q, f (a i) :=
      OAI.PiExponent.DeterminantContradiction.FiniteTranslation.positive_bounded_sum_eq_logMajorant_composition_sum_generic
        q k f