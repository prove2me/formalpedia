-- Prove2me | solution 2 for OAI.PiExponent.FormalInterpolation.coordinateNormalColumnAtPrime_finrank_eq_height
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T07:41:05.556593+00:00
-- url     : https://prove2.me/submissions/d95d6da9-c2d3-4b68-b02d-c7f74bfe421a

import Theorems.Thm_OAI_PiExponent_FormalInterpolation_coordinateNormalColumn_span_finrank_eq_height
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_coordinateNormalColumn_span_finrank_add_trdeg_toNat
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

open OAI.PiExponent.FormalInterpolation

open scoped BigOperators
theorem solution
    {m : Nat}
    (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime] :
    Module.finrank (OAI.PiExponent.FormalInterpolation.logarithmicPrimeField P)
      (Submodule.span (OAI.PiExponent.FormalInterpolation.logarithmicPrimeField P)
        (Set.range (OAI.PiExponent.FormalInterpolation.coordinateNormalColumnAtPrime P))) =
      P.height.toNat := by
  rw [← coordinateNormalColumn_span_finrank_eq_height P]
  rfl
