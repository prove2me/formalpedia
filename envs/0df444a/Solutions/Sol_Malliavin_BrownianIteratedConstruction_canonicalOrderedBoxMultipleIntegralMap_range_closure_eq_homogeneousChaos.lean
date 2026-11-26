-- Prove2me | solution 1 for Malliavin.BrownianIteratedConstruction.canonicalOrderedBoxMultipleIntegralMap_range_closure_eq_homogeneousChaos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:40:09.477571+00:00
-- url     : https://prove2.me/submissions/34dca96a-e765-4dc1-b190-4990f03be69d

import Definitions.Def_Malliavin_BrownianMultipleIntegralBox
import Definitions.Def_Malliavin_BrownianMultipleIntegralBoxSpan
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_canonicalOrderedBoxMultipleIntegralMap_eq_orderedBoxToRandom
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianOrderedBoxOrderRange_closure_eq_homogeneousChaos

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
omit [CompleteSpace W] [BorelSpace W]
namespace Malliavin.BrownianIteratedConstruction
theorem _root_.solution
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t)) (n : ℕ) :
    (LinearMap.range
        (canonicalOrderedBoxMultipleIntegralMap hB (n + 1))).topologicalClosure =
      (brownianHomogeneousChaos hB (n + 1) : Submodule ℝ (RandomL2 P)) := by
  rw [canonicalOrderedBoxMultipleIntegralMap_eq_orderedBoxToRandom hB hsm]
  exact brownianOrderedBoxOrderRange_closure_eq_homogeneousChaos hB hsm n
end Malliavin.BrownianIteratedConstruction
