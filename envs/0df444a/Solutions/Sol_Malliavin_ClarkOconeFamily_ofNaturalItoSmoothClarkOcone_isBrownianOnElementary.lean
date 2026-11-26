-- Prove2me | solution 1 for Malliavin.ClarkOconeFamily.ofNaturalItoSmoothClarkOcone_isBrownianOnElementary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:58:55.514819+00:00
-- url     : https://prove2.me/submissions/5e78d508-4134-4c51-b10d-0adcaec90996

import Definitions.Def_Malliavin_KernelIdentification
import Definitions.Def_Malliavin_NaturalClarkOcone
import Theorems.Thm_Malliavin_ClarkOconeFamily_isBrownianOnElementary_of_itoIntegral_eq_naturalItoIntegral


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
namespace ClarkOconeFamily
theorem _root_.solution
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (generated : IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (hCore : SmoothNaturalClarkOcone hB coordinate coordinate_apply generated hsm hnat) :
    (ClarkOconeFamily.ofNaturalItoSmoothClarkOcone
      hB coordinate coordinate_apply generated hsm hnat hCore).IsBrownianOnElementary := by
  apply ClarkOconeFamily.isBrownianOnElementary_of_itoIntegral_eq_naturalItoIntegral
  rfl
end ClarkOconeFamily
end Malliavin
