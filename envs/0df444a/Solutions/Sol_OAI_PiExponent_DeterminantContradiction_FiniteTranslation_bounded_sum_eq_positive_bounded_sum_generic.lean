-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.FiniteTranslation.bounded_sum_eq_positive_bounded_sum_generic
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T20:21:25.430619+00:00
-- url     : https://prove2.me/submissions/f3c67838-8e34-459e-853c-39033e01f778

import Mathlib
import Definitions.Def_OAI_PiExponent_FiniteActualTranslation

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation


theorem solution (q k : ℕ) (f : ℕ → ℂ) (h0 : f 0 = 0) :
    (∑ a ∈ (Finset.univ : Finset (Fin q → Fin (k + 1))).filter
      (fun a => (∑ i : Fin q, (a i : ℕ)) = k), ∏ i : Fin q, f (a i)) =
      ∑ a ∈ ((Finset.univ : Finset (Fin q → Fin (k + 1))).filter
        (fun a => (∑ i : Fin q, (a i : ℕ)) = k)).filter
          (fun a => ∀ i : Fin q, 0 < (a i : ℕ)), ∏ i : Fin q, f (a i) := by
  classical
  symm
  apply Finset.sum_filter_of_ne
  intro a _ hne i
  by_contra h
  apply hne
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  have : (a i : ℕ) = 0 := by omega
  rw [this, h0]

