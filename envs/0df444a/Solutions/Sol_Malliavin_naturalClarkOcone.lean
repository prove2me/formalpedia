-- Prove2me | solution 1 for Malliavin.naturalClarkOcone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:37:12.311785+00:00
-- url     : https://prove2.me/submissions/30ef43c4-96e9-477e-9232-b91eb5471e4f

import Definitions.Def_Malliavin_NaturalItoRange
import Definitions.Def_Malliavin_ClarkOconeExamples
import Definitions.Def_Malliavin_NaturalItoDuality
import Theorems.Thm_Malliavin_naturalMartingaleRepresentation_canonical


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
namespace Malliavin
theorem _root_.solution
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (generated : IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (hMRT : NaturalMartingaleRepresentation hB hsm hnat)
    (F : D12 P)
    (hBest : bestNaturalItoIntegrand hB hsm hnat (centeredPartL2 F.1) =
      predictableProjection 𝓅
        (timeDerivative hB coordinate coordinate_apply generated
          (mderivD12 P F))) :
    F.1 = expectationL2 F.1 + naturalItoIntegral hB hsm hnat
      (predictableProjection 𝓅
        (timeDerivative hB coordinate coordinate_apply generated
          (mderivD12 P F))) := by
  rw [← hBest]
  exact naturalMartingaleRepresentation_canonical hB hsm hnat hMRT F.1
end Malliavin
