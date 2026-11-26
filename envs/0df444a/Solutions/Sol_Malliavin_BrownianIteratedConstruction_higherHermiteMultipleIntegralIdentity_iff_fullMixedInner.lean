-- Prove2me | solution 1 for Malliavin.BrownianIteratedConstruction.higherHermiteMultipleIntegralIdentity_iff_fullMixedInner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:38:55.400747+00:00
-- url     : https://prove2.me/submissions/fa192a4c-fc70-4b1f-9255-9af3c49d4dae

import Definitions.Def_Malliavin_BrownianWickIsometry
import Definitions.Def_Malliavin_BrownianPurePowerRecurrence
import Definitions.Def_Malliavin_BrownianWickPurePowerComparison
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_wickPurePowerMixedInnerIdentity_iff_higher
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_higherHermiteMultipleIntegralIdentity_iff_mixedInner

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin Malliavin.BrownianIteratedConstruction
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}
namespace Malliavin.BrownianIteratedConstruction
theorem _root_.solution
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t)) :
    BrownianHigherHermiteMultipleIntegralIdentity hB ↔
      BrownianWickPurePowerMixedInnerIdentity hB := by
  calc
    BrownianHigherHermiteMultipleIntegralIdentity hB ↔
        BrownianHigherWickPurePowerMixedInnerIdentity hB :=
      higherHermiteMultipleIntegralIdentity_iff_mixedInner hB hsm
    _ ↔ BrownianWickPurePowerMixedInnerIdentity hB :=
      (wickPurePowerMixedInnerIdentity_iff_higher hB hsm).symm
end Malliavin.BrownianIteratedConstruction
