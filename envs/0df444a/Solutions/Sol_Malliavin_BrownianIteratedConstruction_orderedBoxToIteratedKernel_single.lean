-- Prove2me | solution 1 for Malliavin.BrownianIteratedConstruction.orderedBoxToIteratedKernel_single
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:40:05.30549+00:00
-- url     : https://prove2.me/submissions/5f1ee43a-3643-4080-88c5-2fde783d6fea

import Definitions.Def_Malliavin_BrownianMultipleIntegralBox
import Definitions.Def_Malliavin_BrownianMultipleIntegralBoxSpan

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
omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [MeasurableSpace W]
    [BorelSpace W] [SecondCountableTopology W] [IsGaussian P]
namespace Malliavin.BrownianIteratedConstruction
theorem _root_.solution {n : ℕ} (a : OrderedBoxIndex n) (c : ℝ) :
    orderedBoxToIteratedKernel n (Finsupp.single a c) = c • boxKernel a.u a.v :=
  Finsupp.linearCombination_single _ _ _
end Malliavin.BrownianIteratedConstruction
