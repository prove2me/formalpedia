-- Prove2me | solution 1 for Malliavin.BrownianIteratedConstruction.brownianWickPurePowerMixedInner_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:34:56.010796+00:00
-- url     : https://prove2.me/submissions/6d56d81c-6967-4251-b03f-db78c29c811a

import Definitions.Def_Malliavin_BrownianWickIsometry
import Definitions.Def_Malliavin_BrownianPurePowerRecurrence
import Definitions.Def_Malliavin_BrownianWickPurePowerComparison
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianWickPowerLp_eq_purePowerIntegral_iff_inner
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianPurePowerIntegral_one_step


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
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (v : ℝ≥0 →₀ ℝ) :
    inner ℝ (brownianWickPowerLp hB v 1)
      (brownianPurePowerIntegral hB 1 (stepToLp v)) =
      (Nat.factorial 1 : ℝ) * (‖stepToLp v‖ ^ 2) ^ 1 := by
  exact (brownianWickPowerLp_eq_purePowerIntegral_iff_inner
    hB hsm v 1).1 (brownianPurePowerIntegral_one_step hB hsm v).symm
end Malliavin.BrownianIteratedConstruction
