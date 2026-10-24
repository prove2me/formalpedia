-- Prove2me | solution 1 for OAI.PiExponent.exists_coordinatewise_injective_centers
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T17:21:42.530768+00:00
-- url     : https://prove2.me/submissions/3a5bc6d3-0564-4804-ab91-5b7a4a221a6b

import Definitions.Def_PiExponent_DeterminantSetup

open scoped BigOperators

theorem solution (m K : ℕ) :
    ∃ c : Fin K → Fin m → ℂ,
      ∀ i : Fin m, Function.Injective (fun j : Fin K => c j i) := by
  refine ⟨fun j _ => (j.val : ℂ), ?_⟩
  intro i j₁ j₂ h
  apply Fin.ext
  exact Nat.cast_injective h