-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.truncatedPolynomialJet_CRT_gluing_of_separating_coordinate
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T22:17:25.954342+00:00
-- url     : https://prove2.me/submissions/d35e872f-d3c9-4cd2-8b80-80cd72e0d9ba

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_truncatedPolynomialJet_separating_coordinate_selectors
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_truncatedPolynomialJet_glue_of_separating_coordinate_selectors
import Mathlib.RingTheory.Ideal.Quotient.Operations

open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem solution
    {m : Nat} (K : Nat) (T : Fin m → Nat)
    (c : Fin K → Fin m → Complex)
    (S : Fin (m + 1) → Nat)
    (Q : Fin K → MvPolynomial (Fin (m + 1)) Complex)
    (hsep : K = 0 ∨ ∃ i : Fin m, Function.Injective (fun j : Fin K => c j i)) :
    ∃ P : MvPolynomial (Fin (m + 1)) Complex,
      ∀ (j : Fin K)
        (a : {a : Fin (m + 1) → Nat // ∀ i, a i < S i}),
        (truncatedPolynomialJet (c j) T P).coeff
            (InterpolationMatrix.exponentVector a.1) =
          (truncatedPolynomialJet (c j) T (Q j)).coeff
            (InterpolationMatrix.exponentVector a.1) := by
  obtain ⟨E, hE⟩ :=
    OAI.PiExponent.FormalInterpolation.truncatedPolynomialJet_separating_coordinate_selectors
      K T c S hsep
  exact
    OAI.PiExponent.FormalInterpolation.truncatedPolynomialJet_glue_of_separating_coordinate_selectors
      K T c S Q E hE