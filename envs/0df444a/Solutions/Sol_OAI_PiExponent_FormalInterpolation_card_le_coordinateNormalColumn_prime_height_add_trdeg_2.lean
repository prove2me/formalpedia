-- Prove2me | solution 2 for OAI.PiExponent.FormalInterpolation.card_le_coordinateNormalColumn_prime_height_add_trdeg
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T07:40:55.400433+00:00
-- url     : https://prove2.me/submissions/ef24616e-5ea6-4834-bf91-250f0ae9cacf

import Theorems.Thm_OAI_PiExponent_FormalInterpolation_coordinateNormalColumn_span_finrank_eq_height
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_coordinateNormalColumn_span_finrank_add_trdeg_toNat
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

open OAI.PiExponent.FormalInterpolation

theorem solution
    {m : Nat}
    (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime] :
    m + 1 ≤ P.height + (Algebra.trdeg Complex (logarithmicPrimeField P)).toNat := by
  rw [← coordinateNormalColumn_span_finrank_eq_height P]
  exact_mod_cast (coordinateNormalColumn_span_finrank_add_trdeg_toNat P).ge
