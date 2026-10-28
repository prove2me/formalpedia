-- Prove2me | solution 2 for OAI.PiExponent.FormalInterpolation.coordinateNormalColumn_prime_height_add_trdeg_eq_card
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T07:40:50.878313+00:00
-- url     : https://prove2.me/submissions/9d01054e-154e-413b-be58-4bbd2e000ec1

import Theorems.Thm_OAI_PiExponent_FormalInterpolation_coordinateNormalColumn_span_finrank_eq_height
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_coordinateNormalColumn_span_finrank_add_trdeg_toNat
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

open OAI.PiExponent.FormalInterpolation

theorem solution
    {m : Nat}
    (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime] :
    P.height + (Algebra.trdeg Complex (logarithmicPrimeField P)).toNat = m + 1 := by
  rw [← coordinateNormalColumn_span_finrank_eq_height P]
  exact_mod_cast coordinateNormalColumn_span_finrank_add_trdeg_toNat P
