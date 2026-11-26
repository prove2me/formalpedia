-- Prove2me | solution 1 for Malliavin.BrownianIteratedConstruction.brownianMultipleIntegralCLM_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:03:06.558113+00:00
-- url     : https://prove2.me/submissions/87ff9338-4a7d-4b61-a954-9804a71861dc

import Definitions.Def_Malliavin_BrownianChaosHilbertSum
import Definitions.Def_Malliavin_BrownianMultipleIntegral

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
omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P]
namespace Malliavin.BrownianIteratedConstruction
theorem _root_.solution
    (hB : IsPreBrownianReal B P) (n : ℕ) (f : IteratedKernel n) :
    brownianMultipleIntegralCLM hB n f =
      (n.factorial : ℝ) • integralCLM hB n
        (symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) n 2 f) :=
  rfl
end Malliavin.BrownianIteratedConstruction
