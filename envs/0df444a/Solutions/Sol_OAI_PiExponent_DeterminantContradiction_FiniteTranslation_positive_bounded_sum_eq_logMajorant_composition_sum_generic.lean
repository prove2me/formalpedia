-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.FiniteTranslation.positive_bounded_sum_eq_logMajorant_composition_sum_generic
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T20:21:42.187821+00:00
-- url     : https://prove2.me/submissions/8b180bb7-0d89-4060-9152-4869056c0048

import Mathlib
import Definitions.Def_OAI_PiExponent_FiniteActualTranslation
import Definitions.Def_OAI_PiExponent_logMajorantCompositions

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation


theorem solution (q k : ℕ) (f : ℕ → ℂ) :
    (∑ a ∈ ((Finset.univ : Finset (Fin q → Fin (k + 1))).filter
      (fun a => (∑ i : Fin q, (a i : ℕ)) = k)).filter
        (fun a => ∀ i : Fin q, 0 < (a i : ℕ)), ∏ i : Fin q, f (a i)) =
      ∑ a ∈ logMajorantCompositions q k, ∏ i : Fin q, f (a i) := by
  classical
  have hinj : Function.Injective (fun (a : Fin q → Fin (k + 1)) (i : Fin q) => (a i : ℕ)) := by
    intro a b h
    funext i
    exact Fin.ext (congrFun h i)
  unfold logMajorantCompositions
  rw [Finset.filter_image, Finset.sum_image (fun a _ b _ h => hinj h), Finset.filter_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  apply Finset.filter_congr
  intro a _
  simp only [Function.comp]
  exact and_comm

