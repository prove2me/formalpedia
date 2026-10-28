-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.coordinateNormalColumn_prime_height_add_trdeg_eq_card
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-25T00:39:13.855987+00:00
-- url     : https://prove2.me/submissions/9ed9d32f-70bd-4219-a472-24fc369b010f

import Definitions.Def_OAI_PiExponent_LogarithmicNormalBases
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_coordinateNormalColumn_prime_height_add_trdeg_le_card
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_card_le_coordinateNormalColumn_prime_height_add_trdeg

open OAI.PiExponent.FormalInterpolation

theorem solution
    {m : Nat}
    (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime] :
    P.height + (Algebra.trdeg Complex (logarithmicPrimeField P)).toNat = m + 1 := by
  exact le_antisymm
    (OAI.PiExponent.FormalInterpolation.coordinateNormalColumn_prime_height_add_trdeg_le_card P)
    (OAI.PiExponent.FormalInterpolation.card_le_coordinateNormalColumn_prime_height_add_trdeg P)