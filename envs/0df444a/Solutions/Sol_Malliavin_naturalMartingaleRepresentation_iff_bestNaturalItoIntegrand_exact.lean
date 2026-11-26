-- Prove2me | solution 1 for Malliavin.naturalMartingaleRepresentation_iff_bestNaturalItoIntegrand_exact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:05:45.915799+00:00
-- url     : https://prove2.me/submissions/82bd2020-35f1-4a33-a84e-bbcb0eedbd94

import Definitions.Def_Malliavin_ItoConsequences
import Definitions.Def_Malliavin_NaturalItoRange
import Theorems.Thm_Malliavin_centeredNaturalItoIntegral_bestNaturalItoIntegrand

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
    NaturalMartingaleRepresentation hB hsm hnat ↔
      ∀ G : (CameronMartin.expectationMap P).ker,
        centeredNaturalItoIntegralIsometry hB hsm hnat
          (bestNaturalItoIntegrand hB hsm hnat G) = G := by
  constructor
  · exact fun hMRT G ↦
      centeredNaturalItoIntegral_bestNaturalItoIntegrand hB hsm hnat hMRT G
  · intro hExact
    rw [naturalMartingaleRepresentation_iff_surjective]
    intro G
    exact ⟨bestNaturalItoIntegrand hB hsm hnat G, hExact G⟩
end Malliavin
