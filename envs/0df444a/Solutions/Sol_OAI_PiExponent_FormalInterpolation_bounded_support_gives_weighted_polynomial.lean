-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.bounded_support_gives_weighted_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T12:48:55.564433+00:00
-- url     : https://prove2.me/submissions/52be36cd-519e-45d5-bd5b-f6fd8640b9dd

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem solution
    {m : Nat} (w0 : Real) (w : Fin m → Real)
    (hw0 : 0 < w0) (hw : ∀ i, 0 < w i) (N : Nat) :
    ∃ C : Real, ∀ P : MvPolynomial (Fin (m + 1)) Complex,
      (∀ a ∈ P.support, ∀ i : Fin (m + 1), a i < N) →
      ∃ Q : WeightedPolynomial w0 w C, Q.val = P := by
  classical
  let C : Real := ∑ i : Fin (m + 1), InterpolationMatrix.columnWeights w0 w i * (N : Real)
  refine ⟨C, ?_⟩
  intro P hP
  refine ⟨⟨P, ?_⟩, rfl⟩
  intro a ha
  calc
    (∑ i : Fin (m + 1), InterpolationMatrix.columnWeights w0 w i * (a i : Real))
        ≤ ∑ i : Fin (m + 1), InterpolationMatrix.columnWeights w0 w i * (N : Real) := by
          apply Finset.sum_le_sum
          intro i hi
          have hle : (a i : Real) ≤ (N : Real) := by
            exact_mod_cast (Nat.le_of_lt (hP a ha i))
          exact mul_le_mul_of_nonneg_left hle (le_of_lt (Fin.cases hw0 hw i))
    _ = C := rfl