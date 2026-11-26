-- Prove2me | solution 1 for Malliavin.BrownianIteratedConstruction.brownianWickChainCompatible_of_hermiteMultipleIntegralIdentity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:33:10.691634+00:00
-- url     : https://prove2.me/submissions/90662903-df38-42c0-a4a6-2cd141b8a5c3

import Definitions.Def_Malliavin_BrownianPurePowerIntegral
import Definitions.Def_Malliavin_BrownianHermiteMultipleIntegral
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianHigherWickChainCompatible_of_hermiteMultipleIntegralIdentity
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianWickChainCompatible_iff_higher


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
    (hid : BrownianHigherHermiteMultipleIntegralIdentity hB) :
    BrownianWickChainCompatible hB := by
  exact (brownianWickChainCompatible_iff_higher hB).2
    (brownianHigherWickChainCompatible_of_hermiteMultipleIntegralIdentity
      hB hsm hid)
end Malliavin.BrownianIteratedConstruction
