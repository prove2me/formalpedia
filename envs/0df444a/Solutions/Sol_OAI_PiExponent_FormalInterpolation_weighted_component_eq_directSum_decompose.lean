-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.weighted_component_eq_directSum_decompose
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T14:04:19.516821+00:00
-- url     : https://prove2.me/submissions/ced06f97-83fa-49f9-9630-a61a4434f3f2

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators

theorem solution
    {d : Nat} (w : Fin d → ℚ)
    [g : GradedRing (MvPolynomial.weightedHomogeneousSubmodule ℂ w)]
    (f : MvPolynomial (Fin d) ℂ) (r : ℚ) :
    MvPolynomial.weightedHomogeneousComponent w r f =
      (DirectSum.decompose (MvPolynomial.weightedHomogeneousSubmodule ℂ w) f r :
        MvPolynomial (Fin d) ℂ) := by
  have hdec :
      g.toDecomposition = MvPolynomial.weightedDecomposition ℂ w :=
    Subsingleton.elim _ _
  rw [hdec]
  exact (MvPolynomial.weightedDecomposition.decompose'_apply ℂ w f r).symm