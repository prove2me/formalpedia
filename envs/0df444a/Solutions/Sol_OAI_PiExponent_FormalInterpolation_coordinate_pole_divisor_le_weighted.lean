-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.coordinate_pole_divisor_le_weighted
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan
-- created : 2026-10-21T05:35:28.890655+00:00
-- url     : https://prove2.me/submissions/f06e7a42-13c0-41c7-9415-fb5f3031211c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_finsum_coordinate_pole_le_weighted
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_coordinate_pole_le_weighted_at_place
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_coordinateWeightedPole_support_finite

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem solution
    {d : Nat} (E : Type) [Field E] [Algebra Complex E]
    [Algebra.EssFiniteType Complex E]
    (htrdeg : Algebra.trdeg Complex E = 1) (x : Fin d → E)
    (hgen : IntermediateField.adjoin Complex (Set.range x) = ⊤)
    (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real)) (k : Fin d) :
    (∑ᶠ nu : PolynomialCurvePlace E,
      max (-(polynomialCurveOrder nu (x k) : Real)) 0) ≤
      (w k : Real) *
        (∑ᶠ nu : PolynomialCurvePlace E, polynomialCurvePole nu x w) := by
  have hs :=
    OAI.PiExponent.FormalInterpolation.coordinateWeightedPole_support_finite
      E htrdeg x hgen w hw k
  have hp :=
    OAI.PiExponent.FormalInterpolation.coordinate_pole_le_weighted_at_place
      x w hw k
  exact OAI.PiExponent.FormalInterpolation.finsum_coordinate_pole_le_weighted
    (w k : Real) (le_of_lt (hw k))
    (fun nu => max (-(polynomialCurveOrder nu (x k) : Real)) 0)
    (fun nu => polynomialCurvePole nu x w)
    hs.1 hs.2 hp
