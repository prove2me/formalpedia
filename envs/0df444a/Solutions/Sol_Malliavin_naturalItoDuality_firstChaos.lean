-- Prove2me | solution 1 for Malliavin.naturalItoDuality_firstChaos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:55:33.894051+00:00
-- url     : https://prove2.me/submissions/7ef2dc24-9f70-4f2d-93f5-7a4dfbe5ac10

import Definitions.Def_Malliavin_NaturalItoRange
import Definitions.Def_Malliavin_ClarkOconeExamples
import Definitions.Def_Malliavin_NaturalItoDuality
import Theorems.Thm_Malliavin_naturalItoDuality_wienerIntegral
import Theorems.Thm_Malliavin_wienerIntegral_wienerIntegralEquiv_symm_apply


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
    (hB : IsPreBrownianReal B P) (L : ℝ≥0 → StrongDual ℝ W)
    (hL : ∀ t w, B t w = L t w) (hgen : IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (Z : firstChaos hB) (U : PredictableProcessL2 𝓅 P) :
    inner ℝ ((Z : RandomL2 P) - expectationL2 (Z : RandomL2 P))
        (naturalItoIntegral hB hsm hnat U) =
      inner ℝ (predictableProjection 𝓅
        (timeDerivative hB L hL hgen
          (mderivClosure P (Z : RandomL2 P)))) U := by
  let g := (wienerIntegralEquiv hB).symm Z
  have hZ : (Z : RandomL2 P) = wienerIntegral hB g :=
    (wienerIntegral_wienerIntegralEquiv_symm_apply hB Z).symm
  rw [hZ]
  exact naturalItoDuality_wienerIntegral hB L hL hgen hsm hnat g U
end Malliavin
