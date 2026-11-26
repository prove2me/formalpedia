-- Prove2me | solution 1 for Malliavin.BrownianIteratedConstruction.purePowerRecurrence_iff_higherHermiteMultipleIntegralIdentity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:36:08.721624+00:00
-- url     : https://prove2.me/submissions/156e1f58-e586-45f0-89eb-7fdb8eba2f55

import Definitions.Def_Malliavin_BrownianHermiteMultipleIntegral
import Definitions.Def_Malliavin_BrownianPurePowerRecurrence
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_higherHermiteMultipleIntegralIdentity_of_purePowerRecurrence
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_purePowerRecurrence_of_higherHermiteMultipleIntegralIdentity

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
      BrownianHigherHermiteMultipleIntegralIdentity hB := by
  exact ⟨higherHermiteMultipleIntegralIdentity_of_purePowerRecurrence hB hsm,
    purePowerRecurrence_of_higherHermiteMultipleIntegralIdentity hB hsm⟩
end Malliavin.BrownianIteratedConstruction
