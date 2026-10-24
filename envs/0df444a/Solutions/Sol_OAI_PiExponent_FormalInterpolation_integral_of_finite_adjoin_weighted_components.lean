-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.integral_of_finite_adjoin_weighted_components
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T09:45:26.20372+00:00
-- url     : https://prove2.me/submissions/91f030ba-57ac-4a1d-b442-6b8f5bfccd3e

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem solution
    {d : Nat} (w : Fin d → Rat) (D : Nat) (m : Nat)
    (g : Fin m → MvPolynomial (Fin d) Complex)
    (hfinite : Module.Finite
      (Algebra.adjoin Complex
        (Set.range (fun j =>
          MvPolynomial.weightedHomogeneousComponent
            (fun k => (w k : ℚ)) (D : ℚ) (g j))))
      (MvPolynomial (Fin d) Complex))
    (i : Fin d) :
    IsIntegral
      (Algebra.adjoin Complex
        (Set.range (fun j =>
          MvPolynomial.weightedHomogeneousComponent
            (fun k => (w k : ℚ)) (D : ℚ) (g j))) :
        Subalgebra Complex (MvPolynomial (Fin d) Complex))
      (MvPolynomial.X i : MvPolynomial (Fin d) Complex) := by
  letI : Module.Finite
      (Algebra.adjoin Complex
        (Set.range (fun j =>
          MvPolynomial.weightedHomogeneousComponent
            (fun k => (w k : ℚ)) (D : ℚ) (g j))))
      (MvPolynomial (Fin d) Complex) := hfinite
  exact IsIntegral.of_finite _ (MvPolynomial.X i)