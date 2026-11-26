-- Prove2me | solution 1 for Malliavin.BrownianIteratedConstruction.brownianPurePowerIntegral_eq_integralCLM
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:27:16.649723+00:00
-- url     : https://prove2.me/submissions/be0adf9b-680c-44d5-bd62-feec1a68bcc1

import Definitions.Def_Malliavin_IteratedKernelPurePower
import Definitions.Def_Malliavin_BrownianPolynomialHermite
import Definitions.Def_Malliavin_BrownianPurePowerIntegral
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianMultipleIntegralCLM_apply
import Theorems.Thm_Malliavin_symmetrizeL_iteratedKernelPurePower


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
omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P]
namespace Malliavin.BrownianIteratedConstruction
theorem _root_.solution
    (hB : IsPreBrownianReal B P) (n : ℕ)
    (f : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    brownianPurePowerIntegral hB n f =
      (n.factorial : ℝ) • integralCLM hB n (iteratedKernelPurePower n f) := by
  rw [brownianPurePowerIntegral, brownianMultipleIntegralCLM_apply,
    symmetrizeL_iteratedKernelPurePower]
end Malliavin.BrownianIteratedConstruction
