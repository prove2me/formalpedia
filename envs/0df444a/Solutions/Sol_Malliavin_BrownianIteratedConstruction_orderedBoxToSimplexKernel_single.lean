-- Prove2me | solution 1 for Malliavin.BrownianIteratedConstruction.orderedBoxToSimplexKernel_single
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:50:31.737495+00:00
-- url     : https://prove2.me/submissions/586d74c3-b833-4cb6-9afe-d328b8f61470

import Definitions.Def_Malliavin_ItoConstruction
import Definitions.Def_Malliavin_BrownianIterated

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}
open Malliavin.BrownianIteratedConstruction
omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [MeasurableSpace W]
    [BorelSpace W] [SecondCountableTopology W] [IsGaussian P]
namespace Malliavin.BrownianIteratedConstruction
theorem _root_.solution {n : ℕ} (a : OrderedBoxIndex n) (c : ℝ) :
    orderedBoxToSimplexKernel n (Finsupp.single a c) = c • orderedBoxSimplexKernel a :=
  Finsupp.linearCombination_single _ _ _
end Malliavin.BrownianIteratedConstruction
