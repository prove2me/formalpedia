-- Prove2me | solution 1 for Malliavin.ClarkOconeFamily.ofNaturalItoPositiveChaosSmoothDuality_isBrownianOnElementary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:59:14.393987+00:00
-- url     : https://prove2.me/submissions/68e9c261-b828-42a2-a692-1b03642ae4a5

import Definitions.Def_Malliavin_NaturalClarkOcone
import Definitions.Def_Malliavin_WienerChaos
import Definitions.Def_Malliavin_ChaosMartingaleRepresentation
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
    (hpositive : ∀ n : ℕ, 0 < n →
      (homogeneousChaos hB n : Submodule ℝ (RandomL2 P)) ≤
        naturalItoRange hB hsm hnat)
    (hDuality : SmoothNaturalItoDuality
      hB coordinate coordinate_apply generated hsm hnat) :
    (ClarkOconeFamily.ofNaturalItoPositiveChaosSmoothDuality
      hB coordinate coordinate_apply generated hsm hnat hpositive hDuality
      ).IsBrownianOnElementary := by
  apply ClarkOconeFamily.isBrownianOnElementary_of_itoIntegral_eq_naturalItoIntegral
  rfl
end ClarkOconeFamily
end Malliavin
