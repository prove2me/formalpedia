-- Prove2me | solution 1 for Malliavin.BrownianIteratedConstruction.inner_brownianPurePowerIntegral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:27:18.627839+00:00
-- url     : https://prove2.me/submissions/54f1a2d3-4998-42bc-8f7a-9552113c96f5

import Definitions.Def_Malliavin_IteratedKernelPurePower
import Definitions.Def_Malliavin_BrownianPolynomialHermite
import Definitions.Def_Malliavin_BrownianPurePowerIntegral
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_inner_brownianMultipleIntegralCLM
import Theorems.Thm_Malliavin_inner_iteratedKernelPurePower
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
omit [CompleteSpace W] [BorelSpace W]
namespace Malliavin.BrownianIteratedConstruction
theorem _root_.solution
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (n : ℕ) (f g : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    inner ℝ (brownianPurePowerIntegral hB n f)
        (brownianPurePowerIntegral hB n g) =
      (n.factorial : ℝ) * inner ℝ f g ^ n := by
  rw [brownianPurePowerIntegral, brownianPurePowerIntegral,
    inner_brownianMultipleIntegralCLM hB hsm,
    symmetrizeL_iteratedKernelPurePower, symmetrizeL_iteratedKernelPurePower,
    inner_iteratedKernelPurePower]
end Malliavin.BrownianIteratedConstruction
