-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.mvPolynomial_prime_height_add_card_of_coordinate_algIndependent
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-25T01:00:00.667861+00:00
-- url     : https://prove2.me/submissions/adbeb8e1-004a-430f-a820-51ab7a66acf7

import Definitions.Def_OAI_PiExponent_LogarithmicNormalBases
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_mvPolynomial_prime_height_add_trdeg

open OAI.PiExponent.FormalInterpolation

theorem solution
    {m : Nat}
    (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime]
    (s : Finset (Fin (m + 1)))
    (hs : AlgebraicIndependent Complex
      (fun i : s => algebraMap (MvPolynomial (Fin (m + 1)) Complex)
        (logarithmicPrimeField P) (MvPolynomial.X i.1)))
    (hcard : s.card =
      (Algebra.trdeg Complex (logarithmicPrimeField P)).toNat) :
    m + 1 ≤ P.height + s.card := by
  rw [hcard]
  exact OAI.PiExponent.FormalInterpolation.mvPolynomial_prime_height_add_trdeg P