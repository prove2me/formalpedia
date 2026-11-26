-- Prove2me | solution 1 for Malliavin.BrownianIteratedConstruction.brownianIteratedIntegralFamily_isBrownian
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:58:10.709602+00:00
-- url     : https://prove2.me/submissions/e5410aa7-0cc3-4ced-941e-099821155d85

import Definitions.Def_Malliavin_BrownianIterated
import Definitions.Def_Malliavin_BrownianOrderedBoxDensity
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_family_isBrownian


set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal symmDiff
open Malliavin Malliavin.BrownianIteratedConstruction
namespace Malliavin.BrownianIteratedConstruction
theorem _root_.solution
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
    [SecondCountableTopology W]
    {P : Measure W} [IsGaussian P] {B : ℝ≥0 → W → ℝ}
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t)) :
    (brownianIteratedIntegralFamily hB hsm).IsBrownian B :=
  family_isBrownian hB hsm positiveOrderedBoxDense
end Malliavin.BrownianIteratedConstruction
