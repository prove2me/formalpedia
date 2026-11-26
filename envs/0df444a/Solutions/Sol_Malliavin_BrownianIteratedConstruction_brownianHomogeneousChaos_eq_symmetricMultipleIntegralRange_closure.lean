-- Prove2me | solution 1 for Malliavin.BrownianIteratedConstruction.brownianHomogeneousChaos_eq_symmetricMultipleIntegralRange_closure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:36:16.96921+00:00
-- url     : https://prove2.me/submissions/b2ac2072-c7dd-43d9-94e3-aade5bd1aa85

import Definitions.Def_Malliavin_BrownianChaosHilbertSum
import Definitions.Def_Malliavin_BrownianMultipleIntegral
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianSymmetricMultipleIntegralRange_eq

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
    (hB : IsPreBrownianReal B P) (n : ℕ) :
    (brownianHomogeneousChaos hB n : Submodule ℝ (RandomL2 P)) =
      (brownianSymmetricMultipleIntegralRange hB n).topologicalClosure := by
  unfold brownianHomogeneousChaos
  change (brownianMultipleIntegralRange hB n).topologicalClosure =
    (brownianSymmetricMultipleIntegralRange hB n).topologicalClosure
  rw [brownianSymmetricMultipleIntegralRange_eq hB n]
end Malliavin.BrownianIteratedConstruction
