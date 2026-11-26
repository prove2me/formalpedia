-- Prove2me | solution 1 for Malliavin.BrownianIteratedConstruction.brownianChaosTotal_iff_dense_orderedChainSpan
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:23:49.884565+00:00
-- url     : https://prove2.me/submissions/283517ea-a2cf-4021-9c6d-2169bca62398

import Definitions.Def_Malliavin_BrownianChaosMartingaleRepresentation
import Definitions.Def_Malliavin_BrownianChaosTotality
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianOrderedChainSpan_closure_eq_chaosClosure

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
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t)) :
    BrownianChaosTotal hB ↔ Dense (brownianOrderedChainSpan hB : Set (RandomL2 P)) := by
  rw [BrownianChaosTotal, Submodule.dense_iff_topologicalClosure_eq_top,
    brownianOrderedChainSpan_closure_eq_chaosClosure hB hsm]
end Malliavin.BrownianIteratedConstruction
