-- Prove2me | solution 1 for Malliavin.BrownianIteratedConstruction.brownianPurePowerIntegral_one_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:27:40.779989+00:00
-- url     : https://prove2.me/submissions/bc91f38a-acbc-4526-8095-b7638c2506b9

import Definitions.Def_Malliavin_IteratedKernelPurePower
import Definitions.Def_Malliavin_BrownianPolynomialHermite
import Definitions.Def_Malliavin_BrownianPurePowerIntegral
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_kernelToLine_iteratedKernelPurePower_one
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianMultipleIntegralCLM_one_eq_wienerIntegralKernel
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianWickPowerLp_one
import Theorems.Thm_Malliavin_wienerIntegralKernel_apply


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
    brownianPurePowerIntegral hB 1 (stepToLp v) = brownianWickPowerLp hB v 1 := by
  rw [brownianPurePowerIntegral,
    brownianMultipleIntegralCLM_one_eq_wienerIntegralKernel hB hsm,
    wienerIntegralKernel_apply, kernelToLine_iteratedKernelPurePower_one,
    wienerIntegral_stepToLp, brownianWickPowerLp_one]
end Malliavin.BrownianIteratedConstruction
