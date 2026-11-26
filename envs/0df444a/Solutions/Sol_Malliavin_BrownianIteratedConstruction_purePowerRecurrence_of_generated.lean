-- Prove2me | solution 1 for Malliavin.BrownianIteratedConstruction.purePowerRecurrence_of_generated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:46:38.601751+00:00
-- url     : https://prove2.me/submissions/53a1de92-2477-4415-b670-720af2924402

import Definitions.Def_Malliavin_BrownianWickPurePowerComparison
import Definitions.Def_Malliavin_BrownianMultipleIntegralBoxSpan
import Definitions.Def_Malliavin_PastCylinderDensity
import Definitions.Def_Malliavin_BrownianPurePowerDuality
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_higherHermiteMultipleIntegralIdentity_of_generated
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_purePowerRecurrence_of_higherHermiteMultipleIntegralIdentity


set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
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
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (generated : IsWienerGenerated B) (hsm : ∀ t, StronglyMeasurable (B t)) :
    BrownianPurePowerHermiteRecurrence hB :=
  purePowerRecurrence_of_higherHermiteMultipleIntegralIdentity hB hsm
    (higherHermiteMultipleIntegralIdentity_of_generated
      hB coordinate coordinate_apply generated hsm)
end Malliavin.BrownianIteratedConstruction
