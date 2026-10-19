-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.truncatedPolynomialJet_CRT_gluing
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T22:08:21.775106+00:00
-- url     : https://prove2.me/submissions/7be5eb7e-e3ab-4eb3-8524-8fe43baf0704

import Theorems.Thm_OAI_PiExponent_FormalInterpolation_truncatedPolynomialJet_CRT_gluing_of_separating_coordinate
import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.RingTheory.Ideal.Quotient.Operations

open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem solution
    {m : Nat} (K : Nat) (T : Fin m → Nat) (r : Fin m → Complex)
    (S : Fin (m + 1) → Nat)
    (Q : Fin K → MvPolynomial (Fin (m + 1)) Complex)
    (hr : ∃ i, r i ≠ 0) :
    ∃ P : MvPolynomial (Fin (m + 1)) Complex,
      ∀ (j : Fin K)
        (a : {a : Fin (m + 1) → Nat // ∀ i, a i < S i}),
        (truncatedPolynomialJet (fun i => (j.val : Complex) * r i) T P).coeff
            (InterpolationMatrix.exponentVector a.1) =
          (truncatedPolynomialJet (fun i => (j.val : Complex) * r i) T (Q j)).coeff
            (InterpolationMatrix.exponentVector a.1) := by
  obtain ⟨i, hi⟩ := hr
  apply truncatedPolynomialJet_CRT_gluing_of_separating_coordinate
    (K := K) (T := T)
    (c := fun j k => (j.val : Complex) * r k)
    (S := S) (Q := Q)
  right
  refine ⟨i, ?_⟩
  intro j₁ j₂ heq
  apply Fin.ext
  apply (Nat.cast_injective (R := Complex))
  exact mul_right_cancel₀ hi heq