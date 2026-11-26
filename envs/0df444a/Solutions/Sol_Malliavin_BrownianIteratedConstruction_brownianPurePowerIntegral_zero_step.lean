-- Prove2me | solution 1 for Malliavin.BrownianIteratedConstruction.brownianPurePowerIntegral_zero_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:30:39.706555+00:00
-- url     : https://prove2.me/submissions/724792ca-6d96-4d62-a243-6e0983fda3da

import Definitions.Def_Malliavin_IteratedKernelPurePower
import Definitions.Def_Malliavin_BrownianPolynomialHermite
import Definitions.Def_Malliavin_BrownianPurePowerIntegral
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianPurePowerIntegral_zero
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianWickPowerLp_zero


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
omit [CompleteSpace W] [BorelSpace W] [SecondCountableTopology W]
namespace Malliavin.BrownianIteratedConstruction
theorem _root_.solution
    (hB : IsPreBrownianReal B P) (v : ℝ≥0 →₀ ℝ) :
    brownianPurePowerIntegral hB 0 (stepToLp v) = brownianWickPowerLp hB v 0 := by
  rw [brownianPurePowerIntegral_zero, brownianWickPowerLp_zero]
end Malliavin.BrownianIteratedConstruction
