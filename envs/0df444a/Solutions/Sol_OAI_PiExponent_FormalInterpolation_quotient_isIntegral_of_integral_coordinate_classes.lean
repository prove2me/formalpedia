-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.quotient_isIntegral_of_integral_coordinate_classes
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T16:03:08.68475+00:00
-- url     : https://prove2.me/submissions/aa523570-c6b9-48f6-b661-428708018211

import Mathlib
import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem solution
    {m : Nat}
    (J : Ideal (MvPolynomial (Fin (m + 1)) Complex))
    (hcoord : ∀ i : Fin (m + 1),
      IsIntegral Complex (Ideal.Quotient.mk J (MvPolynomial.X i))) :
    Algebra.IsIntegral Complex ((MvPolynomial (Fin (m + 1)) Complex) ⧸ J) := by
  constructor
  intro a
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  refine MvPolynomial.induction_on (motive := fun p => IsIntegral Complex (Ideal.Quotient.mk J p)) p ?_ ?_ ?_
  · intro c
    have : Ideal.Quotient.mk J (MvPolynomial.C c) =
        algebraMap Complex ((MvPolynomial (Fin (m + 1)) Complex) ⧸ J) c := rfl
    rw [this]
    exact isIntegral_algebraMap
  · intro p q hp hq
    rw [map_add]
    exact hp.add hq
  · intro p i hp
    rw [map_mul]
    exact hp.mul (hcoord i)
