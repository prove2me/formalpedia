-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.adjoin_eq_aeval_range
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T09:10:02.836175+00:00
-- url     : https://prove2.me/submissions/152864a4-eeaa-4d3c-ad2a-248fe1426c3e

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open OAI.PiExponent.FormalInterpolation

theorem solution
    {d m : Nat} (g : Fin m → MvPolynomial (Fin d) Complex)
    (c : Algebra.adjoin Complex (Set.range g)) :
    ∃ F : MvPolynomial (Fin m) Complex,
      MvPolynomial.aeval g F = (c : MvPolynomial (Fin d) Complex) := by
  let x : MvPolynomial (Fin d) Complex := (c : MvPolynomial (Fin d) Complex)
  have hx : x ∈ Algebra.adjoin Complex (Set.range g) := c.2
  rw [Algebra.adjoin_range_eq_range_aeval Complex g] at hx
  exact hx