-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplex_coordinate_power_integral
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T07:50:38.110558+00:00
-- url     : https://prove2.me/submissions/53d3bd27-92d1-43f4-b3de-9b88e4d320c8

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open Filter Topology
open scoped BigOperators

theorem solution (n : Nat) :
    (∫ t in (0 : Real)..1, (1 - t) ^ n) = 1 / (n + 1 : Real) := by
  calc
    (∫ t in (0 : Real)..1, (1 - t) ^ n) =
        ∫ x in ((1 : Real) - 1)..((1 : Real) - 0), x ^ n := by
      simpa using
        (intervalIntegral.integral_comp_sub_left
          (f := fun x : Real => x ^ n) (a := (0 : Real)) (b := 1) (d := (1 : Real)))
    _ = 1 / (n + 1 : Real) := by
      simp [integral_pow]