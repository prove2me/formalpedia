-- Prove2me | solution 1 for Malliavin.BrownianIteratedConstruction.integralCLM_mem_brownianHomogeneousChaos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:47:28.379847+00:00
-- url     : https://prove2.me/submissions/f9b1992b-b1e5-48d4-ae73-89d394e0c549

import Definitions.Def_Malliavin_BrownianOrderedBoxDensity
import Definitions.Def_Malliavin_NaturalClarkOcone
import Definitions.Def_Malliavin_NaturalItoRange
import Definitions.Def_Malliavin_BrownianChaos

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
    integralCLM hB n f ∈ brownianHomogeneousChaos hB n := by
  apply Submodule.le_topologicalClosure (brownianMultipleIntegralRange hB n)
  exact LinearMap.mem_range_self (integralCLM hB n).toLinearMap f
end Malliavin.BrownianIteratedConstruction
