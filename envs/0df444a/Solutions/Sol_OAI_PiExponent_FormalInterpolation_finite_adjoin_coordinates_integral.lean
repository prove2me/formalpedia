-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.finite_adjoin_coordinates_integral
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T18:05:50.215017+00:00
-- url     : https://prove2.me/submissions/44fb23c5-53b9-4fe0-a017-1a10db4e499c

import Mathlib

theorem solution
    {d m : Nat} (g : Fin m → MvPolynomial (Fin d) Complex)
    (hfinite : Module.Finite
      (Algebra.adjoin Complex (Set.range g))
      (MvPolynomial (Fin d) Complex)) :
    ∀ i : Fin d,
      IsIntegral (Algebra.adjoin Complex (Set.range g))
        (MvPolynomial.X i : MvPolynomial (Fin d) Complex) := by
  letI : Module.Finite
      (Algebra.adjoin Complex (Set.range g))
      (MvPolynomial (Fin d) Complex) := hfinite
  intro i
  exact IsIntegral.of_finite (Algebra.adjoin Complex (Set.range g)) (MvPolynomial.X i)