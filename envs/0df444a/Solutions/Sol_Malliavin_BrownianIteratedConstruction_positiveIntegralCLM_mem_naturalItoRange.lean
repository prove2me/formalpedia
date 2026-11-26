-- Prove2me | solution 1 for Malliavin.BrownianIteratedConstruction.positiveIntegralCLM_mem_naturalItoRange
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:52:32.725456+00:00
-- url     : https://prove2.me/submissions/8014a879-e7a8-4b27-900c-76604d05e43c

import Definitions.Def_Malliavin_BrownianOrderedBoxDensity
import Definitions.Def_Malliavin_NaturalClarkOcone
import Definitions.Def_Malliavin_NaturalItoRange
import Definitions.Def_Malliavin_BrownianChaos
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_simplexIntegral_mem_naturalItoRange_succ

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
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm) (n : ℕ) (f : IteratedKernel (n + 1)) :
    positiveIntegralCLM hB n f ∈ naturalItoRange hB hsm hnat := by
  exact simplexIntegral_mem_naturalItoRange_succ hB hsm hnat
    (restrictToSimplex (n + 1) f)
end Malliavin.BrownianIteratedConstruction
