-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.function_divisor_le_weighted_poles
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-21T03:57:53.384389+00:00
-- url     : https://prove2.me/submissions/74663ff6-2c3a-4598-9442-2d972c4f51d4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_OAI_PiExponent_FormalInterpolation_principal_divisor_positive_order_eq_coordinate_poles
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_coordinate_pole_divisor_le_weighted

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics
import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.RingTheory.Algebraic.Defs

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem solution
    {d : Nat} (E : Type) [Field E] [Algebra Complex E]
    [Algebra.EssFiniteType Complex E]
    (htrdeg : Algebra.trdeg Complex E = 1) (x : Fin d → E)
    (hgen : IntermediateField.adjoin Complex (Set.range x) = ⊤)
    (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (k : Fin d) (hk : Transcendental Complex (x k)) (b : Complex) :
    (∑ᶠ nu : PolynomialCurvePlace E,
      max (polynomialCurveOrder nu
        (x k - algebraMap Complex E b) : Real) 0) ≤
      (w k : Real) *
        (∑ᶠ nu : PolynomialCurvePlace E, polynomialCurvePole nu x w) := by
  have hdiv :=
    OAI.PiExponent.FormalInterpolation.principal_divisor_positive_order_eq_coordinate_poles
      htrdeg (x k) hk b
  have hweight :=
    OAI.PiExponent.FormalInterpolation.coordinate_pole_divisor_le_weighted
      E htrdeg x hgen w hw k
  rw [hdiv]
  exact hweight