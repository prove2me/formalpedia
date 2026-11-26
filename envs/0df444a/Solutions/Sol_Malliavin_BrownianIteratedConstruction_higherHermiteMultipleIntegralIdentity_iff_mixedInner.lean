-- Prove2me | solution 1 for Malliavin.BrownianIteratedConstruction.higherHermiteMultipleIntegralIdentity_iff_mixedInner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:34:44.65881+00:00
-- url     : https://prove2.me/submissions/154406a0-e564-4a8a-bf7c-eaacad83b6ad

import Definitions.Def_Malliavin_BrownianWickIsometry
import Definitions.Def_Malliavin_BrownianPurePowerRecurrence
import Definitions.Def_Malliavin_BrownianWickPurePowerComparison
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianWickPowerLp_eq_purePowerIntegral_iff_inner

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
omit [CompleteSpace W] [BorelSpace W]
namespace Malliavin.BrownianIteratedConstruction
theorem _root_.solution
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t)) :
    BrownianHigherHermiteMultipleIntegralIdentity hB ↔
      BrownianHigherWickPurePowerMixedInnerIdentity hB := by
  constructor
  · intro hid v n hn
    exact (brownianWickPowerLp_eq_purePowerIntegral_iff_inner
      hB hsm v n).1 (hid v n hn)
  · intro hinner v n hn
    exact (brownianWickPowerLp_eq_purePowerIntegral_iff_inner
      hB hsm v n).2 (hinner v n hn)
end Malliavin.BrownianIteratedConstruction
