-- Prove2me | solution 1 for Malliavin.BrownianIteratedConstruction.inner_brownianWickPowerLp_chainIntegralLp_eq_purePower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:38:56.740994+00:00
-- url     : https://prove2.me/submissions/f49f0db7-b0bc-46e3-a921-2af8432309d4

import Definitions.Def_Malliavin_BrownianWickPurePowerComparison
import Definitions.Def_Malliavin_BrownianMultipleIntegralBoxSpan
import Definitions.Def_Malliavin_PastCylinderDensity
import Definitions.Def_Malliavin_BrownianPurePowerDuality
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_inner_brownianWickPowerLp_chainIntegralLp
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_inner_brownianPurePowerIntegral_chainIntegralLp

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
    (generated : IsWienerGenerated B) (hsm : ∀ t, StronglyMeasurable (B t))
    (v : ℝ≥0 →₀ ℝ) {n : ℕ} (a : OrderedBoxIndex n) :
    inner ℝ (brownianWickPowerLp hB v n) (chainIntegralLp hB a.u a.v) =
      inner ℝ (brownianPurePowerIntegral hB n (stepToLp v))
        (chainIntegralLp hB a.u a.v) := by
  rw [inner_brownianWickPowerLp_chainIntegralLp
      hB coordinate coordinate_apply generated hsm,
    inner_brownianPurePowerIntegral_chainIntegralLp hB hsm]
end Malliavin.BrownianIteratedConstruction
