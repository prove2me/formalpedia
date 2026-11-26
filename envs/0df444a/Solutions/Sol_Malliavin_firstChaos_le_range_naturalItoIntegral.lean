-- Prove2me | solution 1 for Malliavin.firstChaos_le_range_naturalItoIntegral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:52:43.474695+00:00
-- url     : https://prove2.me/submissions/c13504b3-accf-4c36-851c-bb52b99aa501

import Definitions.Def_Malliavin_ItoConstruction
import Definitions.Def_Malliavin_ItoConsequences
import Theorems.Thm_Malliavin_range_naturalItoDeterministicIntegral

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
    firstChaos hB ≤
      LinearMap.range (naturalItoIntegral hB hsm hnat).toLinearMap := by
  rw [← range_naturalItoDeterministicIntegral hB hsm hnat]
  rintro _ ⟨f, rfl⟩
  exact ⟨deterministicPredictableEmbedding 𝓅 f, rfl⟩
end Malliavin
