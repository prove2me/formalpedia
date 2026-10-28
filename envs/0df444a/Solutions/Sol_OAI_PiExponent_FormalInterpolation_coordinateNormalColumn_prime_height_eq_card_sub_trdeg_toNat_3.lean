-- Prove2me | solution 3 for OAI.PiExponent.FormalInterpolation.coordinateNormalColumn_prime_height_eq_card_sub_trdeg_toNat
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T07:41:00.388137+00:00
-- url     : https://prove2.me/submissions/44abc4ef-aa36-4ff4-9f34-ffe7d7587d63

import Theorems.Thm_OAI_PiExponent_FormalInterpolation_coordinateNormalColumn_span_finrank_eq_height
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_coordinateNormalColumn_span_finrank_add_trdeg_toNat
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

open OAI.PiExponent.FormalInterpolation

theorem solution
    {m : Nat}
    (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime] :
    P.height = ↑((m + 1) -
      (Algebra.trdeg Complex (logarithmicPrimeField P)).toNat) := by
  rw [← coordinateNormalColumn_span_finrank_eq_height P]
  have := coordinateNormalColumn_span_finrank_add_trdeg_toNat P
  norm_cast
  omega
