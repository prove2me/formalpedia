-- Prove2me | solution 1 for Malliavin.BrownianIteratedConstruction.brownianWickPurePowerMixedInner_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:34:52.551016+00:00
-- url     : https://prove2.me/submissions/7b73907c-2c9b-449b-b815-7bbc7384a4bb

import Definitions.Def_Malliavin_BrownianWickIsometry
import Definitions.Def_Malliavin_BrownianPurePowerRecurrence
import Definitions.Def_Malliavin_BrownianWickPurePowerComparison
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianWickPowerLp_eq_purePowerIntegral_iff_inner
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianPurePowerIntegral_zero_step


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
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (v : ℝ≥0 →₀ ℝ) :
    inner ℝ (brownianWickPowerLp hB v 0)
      (brownianPurePowerIntegral hB 0 (stepToLp v)) =
      (Nat.factorial 0 : ℝ) * (‖stepToLp v‖ ^ 2) ^ 0 := by
  exact (brownianWickPowerLp_eq_purePowerIntegral_iff_inner
    hB hsm v 0).1 (brownianPurePowerIntegral_zero_step hB v).symm
end Malliavin.BrownianIteratedConstruction
