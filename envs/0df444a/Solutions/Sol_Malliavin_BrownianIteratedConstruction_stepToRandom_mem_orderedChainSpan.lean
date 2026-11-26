-- Prove2me | solution 1 for Malliavin.BrownianIteratedConstruction.stepToRandom_mem_orderedChainSpan
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:26:59.957456+00:00
-- url     : https://prove2.me/submissions/cc64e34b-aa19-4477-858d-c2f6f30d21aa

import Definitions.Def_Malliavin_BrownianHermite
import Definitions.Def_Malliavin_BrownianCylinderDensity
import Definitions.Def_Malliavin_BrownianChaosTotality
import Definitions.Def_Malliavin_BrownianPolynomialHermite
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianLp_mem_orderedChainSpan
import Theorems.Thm_Malliavin_stepToRandom_single


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
omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    [BorelSpace W] [SecondCountableTopology W] [IsGaussian P]
namespace Malliavin.BrownianIteratedConstruction
theorem _root_.solution (hB : IsPreBrownianReal B P)
    (v : ℝ≥0 →₀ ℝ) :
    stepToRandom hB v ∈ brownianOrderedChainSpan hB := by
  induction v using Finsupp.induction with
  | zero =>
      rw [map_zero]
      exact (brownianOrderedChainSpan hB).zero_mem
  | single_add t c v _ _ ih =>
      rw [map_add, stepToRandom_single]
      exact (brownianOrderedChainSpan hB).add_mem
        ((brownianOrderedChainSpan hB).smul_mem c
          (brownianLp_mem_orderedChainSpan hB t)) ih
end Malliavin.BrownianIteratedConstruction
