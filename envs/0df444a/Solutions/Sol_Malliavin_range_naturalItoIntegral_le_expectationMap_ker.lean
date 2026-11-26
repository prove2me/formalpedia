-- Prove2me | solution 1 for Malliavin.range_naturalItoIntegral_le_expectationMap_ker
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:50:27.650614+00:00
-- url     : https://prove2.me/submissions/34e83b54-6d1f-4d78-a703-ef0a63898b84

import Definitions.Def_Malliavin_ItoConstruction
import Definitions.Def_Malliavin_ItoConsequences
import Theorems.Thm_Malliavin_CameronMartin_expectationMap_apply
attribute [local simp] Malliavin.CameronMartin.expectationMap_apply



set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}
omit [CompleteSpace W] [BorelSpace W]
namespace Malliavin
theorem _root_.solution
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm) :
    LinearMap.range (naturalItoIntegral hB hsm hnat).toLinearMap ≤
      (CameronMartin.expectationMap P).ker := by
  rintro _ ⟨U, rfl⟩
  rw [LinearMap.mem_ker]
  change CameronMartin.expectationMap P (naturalItoIntegral hB hsm hnat U) = 0
  rw [CameronMartin.expectationMap_apply]
  exact integral_naturalItoIntegral hB hsm hnat U
end Malliavin
