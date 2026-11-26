-- Prove2me | solution 1 for Malliavin.ClarkOconeFamily.inner_elementaryIntegralValue_eq_inner_elementaryPredictable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:04:00.541047+00:00
-- url     : https://prove2.me/submissions/72ffe0cf-db51-409a-b884-20679a2820a7

import Definitions.Def_Malliavin_ElementaryIto
import Definitions.Def_Malliavin_PredictableDensity
import Definitions.Def_Malliavin_ItoConstruction
import Theorems.Thm_Malliavin_ClarkOconeFamily_elementaryIntegralValue_eq_elementaryBrownianValue


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
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›} (C : ClarkOconeFamily B P 𝓕)
    {a b c d : ℝ≥0} (hab : a ≤ b) (hcd : c ≤ d)
    (Z : lpMeas ℝ ℝ (𝓕 a) 2 P) (Y : lpMeas ℝ ℝ (𝓕 c) 2 P) :
    inner ℝ (C.elementaryIntegralValue hab Z) (C.elementaryIntegralValue hcd Y) =
      inner ℝ (elementaryPredictable 𝓕 a b Z)
        (elementaryPredictable 𝓕 c d Y) := by
  rw [C.elementaryIntegralValue_eq_elementaryBrownianValue,
    C.elementaryIntegralValue_eq_elementaryBrownianValue]
  exact inner_elementaryBrownianValue_eq_inner_elementaryPredictable
    C.isPreBrownian C.stronglyMeasurable C.naturalFiltration hab hcd Z Y
end ClarkOconeFamily
end Malliavin
