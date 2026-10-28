-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.coordinateNormalColumn_span_finrank_add_trdeg_toNat
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-25T00:26:17.606435+00:00
-- url     : https://prove2.me/submissions/45bcc318-8d7d-45d9-8d56-b1b427c22114

import Definitions.Def_OAI_PiExponent_LogarithmicNormalBases
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.Extension.Cotangent.Basic
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_coordinateNormalColumn_span_finrank_eq_complementary_trdeg
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_trdeg_coordinate_bound

open OAI.PiExponent.FormalInterpolation
theorem solution
    {m : Nat}
    (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime] :
    Module.finrank (logarithmicPrimeField P)
      (Submodule.span (logarithmicPrimeField P)
        (Set.range (coordinateNormalColumnAtPrime P))) +
      (Algebra.trdeg Complex (logarithmicPrimeField P)).toNat = m + 1 := by
  have hrank := coordinateNormalColumn_span_finrank_eq_complementary_trdeg (m := m) P
  have htrdeg := trdeg_coordinate_bound (m := m) P
  omega