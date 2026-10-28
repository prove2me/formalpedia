-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.coordinateNormalColumn_span_finrank_eq_complementary_trdeg
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-25T00:35:20.50752+00:00
-- url     : https://prove2.me/submissions/15b68b50-8ef3-4013-ad16-9e61b68fe403

import Definitions.Def_OAI_PiExponent_LogarithmicNormalBases
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.Extension.Cotangent.Basic
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_coordinateNormalColumn_span_finrank_add_kaehler_finrank
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_fraction_field_kaehler_finrank_eq_trdeg

open scoped BigOperators

 theorem solution
    {m : Nat}
    (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime] :
    Module.finrank (OAI.PiExponent.FormalInterpolation.logarithmicPrimeField P)
      (Submodule.span (OAI.PiExponent.FormalInterpolation.logarithmicPrimeField P)
        (Set.range (OAI.PiExponent.FormalInterpolation.coordinateNormalColumnAtPrime P))) =
      (m + 1) - (Algebra.trdeg Complex (OAI.PiExponent.FormalInterpolation.logarithmicPrimeField P)).toNat := by
  have hsum :=
    OAI.PiExponent.FormalInterpolation.coordinateNormalColumn_span_finrank_add_kaehler_finrank P
  have hdif :=
    OAI.PiExponent.FormalInterpolation.fraction_field_kaehler_finrank_eq_trdeg P
  rw [hdif] at hsum
  omega