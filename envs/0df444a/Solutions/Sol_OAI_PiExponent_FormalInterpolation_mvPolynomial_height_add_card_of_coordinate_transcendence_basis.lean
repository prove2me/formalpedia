-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.mvPolynomial_height_add_card_of_coordinate_transcendence_basis
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-25T07:16:10.330414+00:00
-- url     : https://prove2.me/submissions/db4cbf34-b6ac-4fb0-9e49-dd6e2289c881

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_mvPolynomial_height_add_fraction_field_trdeg_bound

theorem solution
    {m : Nat}
    (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime]
    (s : Finset (Fin (m + 1)))
    (hs : AlgebraicIndependent Complex
      (fun i : s => algebraMap (MvPolynomial (Fin (m + 1)) Complex)
        (FractionRing (MvPolynomial (Fin (m + 1)) Complex ⧸ P))
        (MvPolynomial.X i.1)))
    (hcard : s.card =
      (Algebra.trdeg Complex
        (FractionRing (MvPolynomial (Fin (m + 1)) Complex ⧸ P))).toNat) :
    m + 1 ≤ P.height + s.card := by
  rw [hcard]
  exact OAI.PiExponent.FormalInterpolation.mvPolynomial_height_add_fraction_field_trdeg_bound P