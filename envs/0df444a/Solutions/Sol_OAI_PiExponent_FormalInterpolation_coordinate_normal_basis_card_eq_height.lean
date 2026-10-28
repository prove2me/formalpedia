-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.coordinate_normal_basis_card_eq_height
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-25T00:07:01.317414+00:00
-- url     : https://prove2.me/submissions/62ad8d38-0ecf-4b94-8c79-52e71b3f324c

import Definitions.Def_OAI_PiExponent_LogarithmicNormalBases
import Mathlib.RingTheory.Ideal.Height
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_coordinateNormalColumn_span_finrank_eq_height
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_coordinateNormalBasisAtPrime_card_eq_span_finrank

open OAI.PiExponent.FormalInterpolation

theorem solution
    {m : Nat}
    (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime]
    (A : Finset (Fin (m + 1)))
    (hA : coordinateNormalBasisAtPrime P A) :
    A.card = P.height := by
  let K := logarithmicPrimeField P
  have hdim :
      Module.finrank K (Submodule.span K (Set.range (coordinateNormalColumnAtPrime P))) = P.height := by
    exact OAI.PiExponent.FormalInterpolation.coordinateNormalColumn_span_finrank_eq_height P
  have hcard :
      A.card = Module.finrank K
        (Submodule.span K (Set.range (fun i : A => coordinateNormalColumnAtPrime P i))) := by
    exact OAI.PiExponent.FormalInterpolation.coordinateNormalBasisAtPrime_card_eq_span_finrank P A hA
  have hcard' :
      A.card = Module.finrank K
        (Submodule.span K (Set.range (coordinateNormalColumnAtPrime P))) := by
    calc
      A.card = Module.finrank K
          (Submodule.span K (Set.range (fun i : A => coordinateNormalColumnAtPrime P i))) := hcard
      _ = Module.finrank K
          (Submodule.span K (Set.range (coordinateNormalColumnAtPrime P))) := by
        rw [hA.2]
  rw [<- hdim]
  exact_mod_cast hcard'