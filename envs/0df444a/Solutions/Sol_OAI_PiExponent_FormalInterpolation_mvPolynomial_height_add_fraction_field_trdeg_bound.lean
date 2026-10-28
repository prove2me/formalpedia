-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.mvPolynomial_height_add_fraction_field_trdeg_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-25T07:20:07.005982+00:00
-- url     : https://prove2.me/submissions/c2ed67b7-c616-4431-bfb4-eae20661caae

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_mvPolynomial_height_add_fraction_field_trdeg_bound_over_field

theorem solution
    {m : Nat}
    (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime] :
    m + 1 ≤ P.height +
      (Algebra.trdeg Complex
        (FractionRing (MvPolynomial (Fin (m + 1)) Complex ⧸ P))).toNat := by
  exact OAI.PiExponent.FormalInterpolation.mvPolynomial_height_add_fraction_field_trdeg_bound_over_field
    (K := Complex) (n := m + 1) P