-- Prove2me | solution 1 for Malliavin.BrownianIteratedConstruction.dense_orderedChainSpan_of_hermiteMultipleIntegralIdentity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:39:55.497975+00:00
-- url     : https://prove2.me/submissions/6136365a-a51d-4d03-900d-d8acca71e031

import Definitions.Def_Malliavin_BrownianPurePowerIntegral
import Definitions.Def_Malliavin_BrownianHermiteMultipleIntegral
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianWickChainCompatible_of_hermiteMultipleIntegralIdentity
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_dense_orderedChainSpan_of_wickChainCompatible


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
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (hgen : IsWienerGenerated B)
    (hid : BrownianHigherHermiteMultipleIntegralIdentity hB) :
    Dense (brownianOrderedChainSpan hB : Set (RandomL2 P)) := by
  exact dense_orderedChainSpan_of_wickChainCompatible hB hgen
    (brownianWickChainCompatible_of_hermiteMultipleIntegralIdentity
      hB hsm hid)
end Malliavin.BrownianIteratedConstruction
