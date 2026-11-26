-- Prove2me | solution 1 for Malliavin.BrownianIteratedConstruction.inner_brownianPurePowerIntegral_chainIntegralLp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:35:10.441933+00:00
-- url     : https://prove2.me/submissions/295952d5-fc43-4d90-81a0-77e7ba4588b2

import Definitions.Def_Malliavin_BrownianWickPurePowerComparison
import Definitions.Def_Malliavin_BrownianMultipleIntegralBoxSpan
import Definitions.Def_Malliavin_PastCylinderDensity
import Definitions.Def_Malliavin_BrownianPurePowerDuality
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_inner_iteratedKernelPurePower_boxKernel
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianMultipleIntegralCLM_orderedBox
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_inner_brownianMultipleIntegralCLM
import Theorems.Thm_Malliavin_inner_symmetrizeL_left
import Theorems.Thm_Malliavin_symmetrizeL_iteratedKernelPurePower


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
omit [CompleteSpace W] [BorelSpace W]
namespace Malliavin.BrownianIteratedConstruction
theorem _root_.solution
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (f : Lp ℝ 2 nonnegativeLebesgueMeasure) {n : ℕ} (a : OrderedBoxIndex n) :
    inner ℝ (brownianPurePowerIntegral hB n f) (chainIntegralLp hB a.u a.v) =
      (n.factorial : ℝ) *
        ∏ i, inner ℝ f (iocIndicator (a.u i) (a.v i)) := by
  rw [← brownianMultipleIntegralCLM_orderedBox hB hsm a,
    brownianPurePowerIntegral, inner_brownianMultipleIntegralCLM hB hsm,
    symmetrizeL_iteratedKernelPurePower,
    ← inner_symmetrizeL_left n (iteratedKernelPurePower n f) (boxKernel a.u a.v),
    symmetrizeL_iteratedKernelPurePower,
    inner_iteratedKernelPurePower_boxKernel]
end Malliavin.BrownianIteratedConstruction
