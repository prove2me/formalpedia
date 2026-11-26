-- Prove2me | solution 1 for Malliavin.BrownianIteratedConstruction.brownianHigherWickChainCompatible_of_hermiteMultipleIntegralIdentity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:30:14.585076+00:00
-- url     : https://prove2.me/submissions/bc4a74e3-6f82-498b-a977-45f3c915dfbf

import Definitions.Def_Malliavin_BrownianPurePowerIntegral
import Definitions.Def_Malliavin_BrownianHermiteMultipleIntegral
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianHomogeneousChaos_le_orderedChainSpan_closure
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianPurePowerIntegral_mem_brownianHomogeneousChaos


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
    BrownianHigherWickChainCompatible hB := by
  intro v n hn
  rw [hid v n hn]
  exact brownianHomogeneousChaos_le_orderedChainSpan_closure hB hsm n
    (brownianPurePowerIntegral_mem_brownianHomogeneousChaos
      hB n (stepToLp v))
end Malliavin.BrownianIteratedConstruction
