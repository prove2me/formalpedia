-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.coordinateNormalBasisAtPrime_card_eq_span_finrank
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T00:02:08.454796+00:00
-- url     : https://prove2.me/submissions/ccc5d436-f639-4faf-863b-7f652d3ea982

import Definitions.Def_OAI_PiExponent_LogarithmicNormalBases
import Mathlib.RingTheory.Ideal.Height

open OAI.PiExponent.FormalInterpolation

theorem solution
    {m : Nat}
    (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime]
    (A : Finset (Fin (m + 1)))
    (hA : coordinateNormalBasisAtPrime P A) :
    A.card = Module.finrank (logarithmicPrimeField P)
      (Submodule.span (logarithmicPrimeField P)
        (Set.range (fun i : A => coordinateNormalColumnAtPrime P i))) := by
  rw [finrank_span_eq_card hA.1]
  simp
