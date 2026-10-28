-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.coordinateNormalColumn_span_finrank_eq_height
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-25T00:21:36.438137+00:00
-- url     : https://prove2.me/submissions/2abf43b4-8635-4bbc-98c3-6aad7e9fed9b

import Definitions.Def_OAI_PiExponent_LogarithmicNormalBases
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_coordinateNormalColumn_span_finrank_add_trdeg_toNat
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_coordinateNormalColumn_prime_height_eq_card_sub_trdeg_toNat

open OAI.PiExponent.FormalInterpolation

theorem solution
    {m : Nat}
    (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime] :
    Module.finrank (logarithmicPrimeField P)
      (Submodule.span (logarithmicPrimeField P)
        (Set.range (coordinateNormalColumnAtPrime P))) = P.height := by
  have hspan :=
    OAI.PiExponent.FormalInterpolation.coordinateNormalColumn_span_finrank_add_trdeg_toNat
      (P := P)
  have hheight :=
    OAI.PiExponent.FormalInterpolation.coordinateNormalColumn_prime_height_eq_card_sub_trdeg_toNat
      (P := P)
  have hnat :
      Module.finrank (logarithmicPrimeField P)
          (Submodule.span (logarithmicPrimeField P)
            (Set.range (coordinateNormalColumnAtPrime P))) =
        (m + 1) - (Algebra.trdeg Complex (logarithmicPrimeField P)).toNat := by
    omega
  rw [hheight]
  exact_mod_cast hnat