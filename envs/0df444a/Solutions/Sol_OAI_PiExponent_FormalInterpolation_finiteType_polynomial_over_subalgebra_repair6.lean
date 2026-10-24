-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.finiteType_polynomial_over_subalgebra_repair6
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T20:09:50.820676+00:00
-- url     : https://prove2.me/submissions/1bf0753d-c746-4a1f-aa66-82e72ac74ecd

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib

open OAI.PiExponent.FormalInterpolation

open MeasureTheory Filter Topology in

theorem solution
    {d : Nat} (A : Subalgebra Complex (MvPolynomial (Fin d) Complex)) :
    Algebra.FiniteType A (MvPolynomial (Fin d) Complex) := by
  exact Algebra.FiniteType.of_restrictScalars_finiteType Complex A _
