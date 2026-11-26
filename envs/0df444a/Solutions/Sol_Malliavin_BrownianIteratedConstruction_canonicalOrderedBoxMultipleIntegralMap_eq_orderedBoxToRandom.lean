-- Prove2me | solution 1 for Malliavin.BrownianIteratedConstruction.canonicalOrderedBoxMultipleIntegralMap_eq_orderedBoxToRandom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:33:49.78353+00:00
-- url     : https://prove2.me/submissions/c86da7eb-93fa-4f2e-bf40-e0c90749470f

import Definitions.Def_Malliavin_BrownianMultipleIntegralBox
import Definitions.Def_Malliavin_BrownianMultipleIntegralBoxSpan
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianMultipleIntegralCLM_orderedBoxToIteratedKernel

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
    canonicalOrderedBoxMultipleIntegralMap hB n = orderedBoxToRandom hB n := by
  apply LinearMap.ext
  intro c
  exact brownianMultipleIntegralCLM_orderedBoxToIteratedKernel hB hsm n c
end Malliavin.BrownianIteratedConstruction
