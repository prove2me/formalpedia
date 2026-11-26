-- Prove2me | solution 1 for Malliavin.BrownianIteratedConstruction.orderedBoxToRandom_single
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:51:37.244823+00:00
-- url     : https://prove2.me/submissions/55dbf62a-0f06-49e6-8d0e-eb9917961945

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
omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P]
namespace Malliavin.BrownianIteratedConstruction
theorem _root_.solution (hB : IsPreBrownianReal B P)
    {n : ℕ} (a : OrderedBoxIndex n) (c : ℝ) :
    orderedBoxToRandom hB n (Finsupp.single a c) = c • chainIntegralLp hB a.u a.v :=
  Finsupp.linearCombination_single _ _ _
end Malliavin.BrownianIteratedConstruction
