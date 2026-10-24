-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.weightedHomogeneousComponent_mul_of_right_homogeneous
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T09:34:44.064041+00:00
-- url     : https://prove2.me/submissions/6ff0106d-0d46-406e-a1e1-fce46ab11cdb

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_weightedHomogeneousComponent_mul_monomial

open scoped BigOperators

theorem solution
    {d : Nat} (w : Fin d → ℚ) (E D : ℚ)
    (a p : MvPolynomial (Fin d) Complex)
    (hp : MvPolynomial.IsWeightedHomogeneous w p D) :
    MvPolynomial.weightedHomogeneousComponent w E (a * p) =
      MvPolynomial.weightedHomogeneousComponent w (E - D) a * p := by
  classical
  let motive : (q : MvPolynomial (Fin d) Complex) →
      MvPolynomial.IsWeightedHomogeneous w q D → Prop :=
    fun q _ =>
      MvPolynomial.weightedHomogeneousComponent w E (a * q) =
        MvPolynomial.weightedHomogeneousComponent w (E - D) a * q
  have h : motive p hp := by
    refine hp.induction_on (motive := motive) ?_ ?_ ?_
    · simp [motive]
    · intro q r hq hr ihq ihr
      simp [motive, ihq, ihr, mul_add]
    · intro v c hv
      simpa [motive, hv] using
        OAI.PiExponent.FormalInterpolation.weightedHomogeneousComponent_mul_monomial
          w E a v c
  exact h