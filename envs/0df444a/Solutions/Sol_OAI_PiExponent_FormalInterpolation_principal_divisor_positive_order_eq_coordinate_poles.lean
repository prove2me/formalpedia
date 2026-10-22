-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.principal_divisor_positive_order_eq_coordinate_poles
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-21T04:23:32.638711+00:00
-- url     : https://prove2.me/submissions/11efe24e-83df-4f77-bdbb-50bb21c6641e

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics
import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.RingTheory.Algebraic.Defs
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_principal_divisor_positive_eq_poles
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_coordinate_poles_invariant_sub_const

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

noncomputable section

theorem solution
    {E : Type} [Field E] [Algebra Complex E]
    [Algebra.EssFiniteType Complex E]
    (htrdeg : Algebra.trdeg Complex E = 1) (z : E)
    (hz : Transcendental Complex z) (b : Complex) :
    (∑ᶠ nu : PolynomialCurvePlace E,
      max (polynomialCurveOrder nu (z - algebraMap Complex E b) : Real) 0) =
      ∑ᶠ nu : PolynomialCurvePlace E,
        max (-(polynomialCurveOrder nu z : Real)) 0 := by
  calc
    (∑ᶠ nu : PolynomialCurvePlace E,
      max (polynomialCurveOrder nu (z - algebraMap Complex E b) : Real) 0)
        = ∑ᶠ nu : PolynomialCurvePlace E,
          max (-(polynomialCurveOrder nu (z - algebraMap Complex E b) : Real)) 0 :=
            OAI.PiExponent.FormalInterpolation.principal_divisor_positive_eq_poles
              htrdeg (z - algebraMap Complex E b)
    _ = ∑ᶠ nu : PolynomialCurvePlace E,
          max (-(polynomialCurveOrder nu z : Real)) 0 :=
            OAI.PiExponent.FormalInterpolation.coordinate_poles_invariant_sub_const
              htrdeg z hz b