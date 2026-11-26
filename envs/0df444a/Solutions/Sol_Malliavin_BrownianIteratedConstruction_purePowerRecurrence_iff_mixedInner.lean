-- Prove2me | solution 1 for Malliavin.BrownianIteratedConstruction.purePowerRecurrence_iff_mixedInner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:37:41.623334+00:00
-- url     : https://prove2.me/submissions/b928dd45-cd73-4099-bb5b-2a09aa01d78e

import Definitions.Def_Malliavin_BrownianWickIsometry
import Definitions.Def_Malliavin_BrownianPurePowerRecurrence
import Definitions.Def_Malliavin_BrownianWickPurePowerComparison
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_higherHermiteMultipleIntegralIdentity_iff_mixedInner
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_purePowerRecurrence_iff_higherHermiteMultipleIntegralIdentity


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
    BrownianPurePowerHermiteRecurrence hB ↔
      BrownianHigherWickPurePowerMixedInnerIdentity hB := by
  rw [purePowerRecurrence_iff_higherHermiteMultipleIntegralIdentity hB hsm,
    higherHermiteMultipleIntegralIdentity_iff_mixedInner hB hsm]
end Malliavin.BrownianIteratedConstruction
