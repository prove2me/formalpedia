-- Prove2me | solution 1 for Malliavin.ClarkOconeFamily.elementaryIntegralValue_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:32:06.023247+00:00
-- url     : https://prove2.me/submissions/b4ded4e4-3134-4d02-b1c6-f8cbccc3cfa0

import Definitions.Def_Malliavin_ClarkOcone
import Definitions.Def_Malliavin_PredictableDensity
import Theorems.Thm_Malliavin_ClarkOconeFamily_coeFn_elementaryIntegralValue


set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Function
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5
noncomputable section
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
namespace Malliavin
namespace ClarkOconeFamily
theorem _root_.solution
    {B : ℝ≥0 → W → ℝ} {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C D : ClarkOconeFamily B P 𝓕) {a b : ℝ≥0} (hab : a ≤ b)
    (Z : lpMeas ℝ ℝ (𝓕 a) 2 P) :
    C.elementaryIntegralValue hab Z = D.elementaryIntegralValue hab Z := by
  apply Lp.ext
  exact (C.coeFn_elementaryIntegralValue hab Z).trans
    (D.coeFn_elementaryIntegralValue hab Z).symm
end ClarkOconeFamily
end Malliavin
