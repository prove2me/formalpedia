-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.card_le_coordinateNormalColumn_prime_height_add_trdeg
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-25T00:52:52.344078+00:00
-- url     : https://prove2.me/submissions/42975fd8-1c41-4071-a8cb-195853014c79

import Definitions.Def_OAI_PiExponent_LogarithmicNormalBases
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_mvPolynomial_prime_exists_coordinate_trdeg_basis
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_mvPolynomial_prime_height_add_card_of_coordinate_algIndependent
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

open OAI.PiExponent.FormalInterpolation

theorem solution
    {m : Nat}
    (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime] :
    m + 1 ≤ P.height + (Algebra.trdeg Complex (logarithmicPrimeField P)).toNat := by
  obtain ⟨s, hs, hcard⟩ :=
    OAI.PiExponent.FormalInterpolation.mvPolynomial_prime_exists_coordinate_trdeg_basis P
  have h :=
    OAI.PiExponent.FormalInterpolation.mvPolynomial_prime_height_add_card_of_coordinate_algIndependent
      P s hs hcard
  simpa [hcard] using h