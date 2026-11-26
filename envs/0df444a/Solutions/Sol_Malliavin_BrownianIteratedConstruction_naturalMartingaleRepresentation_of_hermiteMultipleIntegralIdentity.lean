-- Prove2me | solution 1 for Malliavin.BrownianIteratedConstruction.naturalMartingaleRepresentation_of_hermiteMultipleIntegralIdentity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:42:16.221395+00:00
-- url     : https://prove2.me/submissions/ada4e3b0-0f88-497b-8d1a-f06f51954c4c

import Definitions.Def_Malliavin_BrownianPurePowerIntegral
import Definitions.Def_Malliavin_BrownianHermiteMultipleIntegral
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianWickChainCompatible_of_hermiteMultipleIntegralIdentity
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_naturalMartingaleRepresentation_of_wickChainCompatible


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
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm) (hgen : IsWienerGenerated B)
    (hid : BrownianHigherHermiteMultipleIntegralIdentity hB) :
    NaturalMartingaleRepresentation hB hsm hnat := by
  exact naturalMartingaleRepresentation_of_wickChainCompatible
    hB hsm hnat hgen
    (brownianWickChainCompatible_of_hermiteMultipleIntegralIdentity
      hB hsm hid)
end Malliavin.BrownianIteratedConstruction
