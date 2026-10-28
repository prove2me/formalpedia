-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.mvPolynomial_prime_height_add_trdeg
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-25T01:06:09.423772+00:00
-- url     : https://prove2.me/submissions/c6423aaa-824a-42cf-a032-6f7b1b3d6be5

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_mvPolynomial_exists_coordinate_transcendence_basis
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_mvPolynomial_height_add_card_of_coordinate_transcendence_basis

open OAI.PiExponent.FormalInterpolation

theorem solution
    {m : Nat}
    (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime] :
    m + 1 ≤ P.height +
      (Algebra.trdeg Complex
        (FractionRing (MvPolynomial (Fin (m + 1)) Complex ⧸ P))).toNat := by
  obtain ⟨s, hs, hcard⟩ :=
    OAI.PiExponent.FormalInterpolation.mvPolynomial_exists_coordinate_transcendence_basis P
  rw [← hcard]
  exact OAI.PiExponent.FormalInterpolation.mvPolynomial_height_add_card_of_coordinate_transcendence_basis
    P s hs hcard