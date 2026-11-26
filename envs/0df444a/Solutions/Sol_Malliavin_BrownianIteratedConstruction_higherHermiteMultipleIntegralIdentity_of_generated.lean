-- Prove2me | solution 1 for Malliavin.BrownianIteratedConstruction.higherHermiteMultipleIntegralIdentity_of_generated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:44:20.709811+00:00
-- url     : https://prove2.me/submissions/86dcdda8-3b38-47f6-9093-4e0466138c41

import Definitions.Def_Malliavin_BrownianWickPurePowerComparison
import Definitions.Def_Malliavin_BrownianMultipleIntegralBoxSpan
import Definitions.Def_Malliavin_PastCylinderDensity
import Definitions.Def_Malliavin_BrownianPurePowerDuality
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianWickPowerLp_eq_purePowerIntegral_of_generated

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
    BrownianHigherHermiteMultipleIntegralIdentity hB := by
  intro v n hn
  exact brownianWickPowerLp_eq_purePowerIntegral_of_generated
    hB coordinate coordinate_apply generated hsm v n
end Malliavin.BrownianIteratedConstruction
