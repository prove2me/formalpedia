-- Prove2me | solution 1 for Malliavin.ClarkOconeFamily.ofNaturalIto_isBrownianOnElementary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:04:57.57872+00:00
-- url     : https://prove2.me/submissions/0541ec39-d206-43f2-9946-6f846778593c

import Definitions.Def_Malliavin_ItoConstruction
import Definitions.Def_Malliavin_ItoConsequences
import Theorems.Thm_Malliavin_ClarkOconeFamily_elementaryIntegralValue_eq_elementaryBrownianValue
import Theorems.Thm_Malliavin_naturalItoIntegral_elementaryPredictable


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
    (hMRT : ∀ G : RandomL2 P, ∃ U : PredictableProcessL2 𝓅 P,
      G = expectationL2 G + naturalItoIntegral hB hsm hnat U)
    (hDuality : ∀ (F : D12 P) (U : PredictableProcessL2 𝓅 P),
      inner ℝ (F.1 - expectationL2 F.1)
          (naturalItoIntegral hB hsm hnat U) =
        inner ℝ (predictableProjection 𝓅
          (Malliavin.timeDerivative hB coordinate coordinate_apply generated
            (mderivD12 P F))) U) :
    (ClarkOconeFamily.ofNaturalIto (W := W) (P := P) (B := B)
      hB coordinate coordinate_apply generated hsm hnat
      hMRT hDuality).IsBrownianOnElementary := by
  intro a b hab Z
  change naturalItoIntegral hB hsm hnat
      (elementaryPredictable 𝓅 a b Z) = _
  rw [naturalItoIntegral_elementaryPredictable]
  exact
    ((ClarkOconeFamily.ofNaturalIto (W := W) (P := P) (B := B)
      hB coordinate coordinate_apply generated hsm hnat hMRT hDuality
      ).elementaryIntegralValue_eq_elementaryBrownianValue hab Z).symm
end ClarkOconeFamily
end Malliavin
