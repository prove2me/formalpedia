-- Prove2me | solution 1 for Malliavin.naturalClarkOcone_condExp_of_generated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:52:54.079705+00:00
-- url     : https://prove2.me/submissions/baf4125a-d960-4cfb-973b-5ef62f52e88e

import Definitions.Def_Malliavin_BrownianHermiteClarkOcone
import Definitions.Def_Malliavin_BrownianPurePowerDuality
import Definitions.Def_Malliavin_ClarkOconeExamples
import Definitions.Def_Malliavin_NaturalFiltrationLeftContinuous
import Definitions.Def_Malliavin_BrownianClarkOconeCapstone
import Theorems.Thm_Malliavin_naturalClarkOcone_of_generated
import Theorems.Thm_Malliavin_exists_representative_predictableDerivative_condExp_natural


set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin
open BrownianIteratedConstruction
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}
namespace Malliavin
theorem _root_.solution
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (generated : IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {filtration : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : filtration = Filtration.natural B hsm)
    (F : D12 P) :
    ∃ G : ℝ≥0 × W → ℝ,
      StronglyMeasurable[filtration.predictable] G ∧
      (predictableProjection filtration
          (timeDerivative hB coordinate coordinate_apply generated (mderivD12 P F)) :
            ℝ≥0 × W → ℝ) =ᵐ[nonnegativeLebesgueMeasure.prod P] G ∧
      (∀ᵐ t ∂nonnegativeLebesgueMeasure, 0 < t →
        (fun w ↦ G (t, w)) =ᵐ[P]
          P[(fun w ↦ (timeDerivative hB coordinate coordinate_apply generated
            (mderivD12 P F)) (t, w)) | filtration t]) ∧
      F.1 = expectationL2 F.1 + naturalItoIntegral hB hsm hnat
        (predictableProjection filtration
          (timeDerivative hB coordinate coordinate_apply generated (mderivD12 P F))) := by
  obtain ⟨G, hG, hGae, hsection⟩ :=
    exists_representative_predictableDerivative_condExp_natural
      (ClarkOconeFamily.ofGenerated hB coordinate coordinate_apply generated hsm hnat) F
  exact ⟨G, hG, hGae, hsection,
    naturalClarkOcone_of_generated hB coordinate coordinate_apply generated hsm hnat F⟩
end Malliavin
