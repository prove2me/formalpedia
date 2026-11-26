-- Prove2me | solution 1 for Malliavin.BrownianIteratedConstruction.brownianPurePowerIntegral_mem_brownianHomogeneousChaos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:28:55.72706+00:00
-- url     : https://prove2.me/submissions/75fa46f1-2ad7-493b-a24c-9a9018966f0d

import Definitions.Def_Malliavin_IteratedKernelPurePower
import Definitions.Def_Malliavin_BrownianPolynomialHermite
import Definitions.Def_Malliavin_BrownianPurePowerIntegral
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianPurePowerIntegral_eq_integralCLM
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_integralCLM_mem_brownianHomogeneousChaos


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
    brownianPurePowerIntegral hB n f ∈ brownianHomogeneousChaos hB n := by
  rw [brownianPurePowerIntegral_eq_integralCLM]
  exact (brownianHomogeneousChaos hB n).smul_mem (n.factorial : ℝ)
    (integralCLM_mem_brownianHomogeneousChaos hB n (iteratedKernelPurePower n f))
end Malliavin.BrownianIteratedConstruction
