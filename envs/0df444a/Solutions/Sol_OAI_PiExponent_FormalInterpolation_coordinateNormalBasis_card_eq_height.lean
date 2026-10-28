-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.coordinateNormalBasis_card_eq_height
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-25T07:11:51.174869+00:00
-- url     : https://prove2.me/submissions/24f95219-83eb-412e-829b-60c624cf47a6

import Definitions.Def_OAI_PiExponent_LogarithmicNormalBases
import Mathlib.RingTheory.Ideal.Height
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_coordinateNormalColumn_span_finrank_eq_prime_height

open OAI.PiExponent.FormalInterpolation

noncomputable section

theorem solution
    {m : Nat} (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime]
    (A : Finset (Fin (m + 1)))
    (hA : coordinateNormalBasisAtPrime P A) :
    (A.card : ℕ∞) = P.height := by
  classical
  have hcard : A.card = Module.finrank (logarithmicPrimeField P)
      (Submodule.span (logarithmicPrimeField P)
        (Set.range (coordinateNormalColumnAtPrime P))) := by
    rw [← hA.2, finrank_span_eq_card hA.1]
    simp
  calc
    (A.card : ℕ∞) =
        (Module.finrank (logarithmicPrimeField P)
          (Submodule.span (logarithmicPrimeField P)
            (Set.range (coordinateNormalColumnAtPrime P))) : ℕ∞) :=
      congrArg (fun n : Nat => (n : ℕ∞)) hcard
    _ = P.height := coordinateNormalColumn_span_finrank_eq_prime_height P