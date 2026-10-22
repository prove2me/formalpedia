-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.logarithmicDegreeBound_X_pderiv_support_v2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-21T13:39:43.095701+00:00
-- url     : https://prove2.me/submissions/3c807fc6-3e2a-44d5-af11-01f33d14ae87

import Definitions.Def_OAI_PiExponent_LogarithmicWordContact

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem solution
    {d : Nat} (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (N : Real) (F : MvPolynomial (Fin d) Complex)
    (hF : logarithmicDegreeBound w N F) (i : Fin d) :
    logarithmicDegreeBound w N
      (MvPolynomial.X i * MvPolynomial.pderiv i F) := by
  intro a ha
  have hi : i ∈ a.support := by
    by_contra hnot
    have hzero :
        MvPolynomial.coeff a (MvPolynomial.X i * MvPolynomial.pderiv i F) = 0 := by
      simp [MvPolynomial.coeff_X_mul', hnot]
    exact (MvPolynomial.mem_support_iff.mp ha) hzero
  have hderiv :
      MvPolynomial.coeff (a - Finsupp.single i 1) (MvPolynomial.pderiv i F) ≠ 0 := by
    have hcoeff :
        MvPolynomial.coeff a (MvPolynomial.X i * MvPolynomial.pderiv i F) ≠ 0 :=
      MvPolynomial.mem_support_iff.mp ha
    simpa [MvPolynomial.coeff_X_mul', hi] using hcoeff
  have hcancel :
      a - Finsupp.single i 1 + Finsupp.single i 1 = a := by
    apply tsub_add_cancel_of_le
    exact Finsupp.single_le_iff.mpr
      (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi))
  have hsource :
      MvPolynomial.coeff a F ≠ 0 := by
    intro hz
    apply hderiv
    simp [MvPolynomial.coeff_pderiv, hcancel, hz]
  have haF : a ∈ F.support := MvPolynomial.mem_support_iff.mpr hsource
  exact hF a haF