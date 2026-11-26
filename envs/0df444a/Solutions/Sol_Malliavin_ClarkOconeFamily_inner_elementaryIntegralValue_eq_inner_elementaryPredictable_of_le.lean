-- Prove2me | solution 1 for Malliavin.ClarkOconeFamily.inner_elementaryIntegralValue_eq_inner_elementaryPredictable_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:31:57.362953+00:00
-- url     : https://prove2.me/submissions/e26cf469-00cd-49b6-881b-94c611da481d

import Definitions.Def_Malliavin_ClarkOcone
import Definitions.Def_Malliavin_ElementaryIto
import Theorems.Thm_Malliavin_ClarkOconeFamily_inner_elementaryIntegralValue_eq_zero_of_le
import Theorems.Thm_Malliavin_inner_elementaryPredictable_eq_zero_of_le

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
    {a b c d : ℝ≥0} (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (Z : lpMeas ℝ ℝ (𝓕 a) 2 P) (Y : lpMeas ℝ ℝ (𝓕 c) 2 P) :
    inner ℝ (C.elementaryIntegralValue hab Z) (C.elementaryIntegralValue hcd Y) =
      inner ℝ (elementaryPredictable 𝓕 a b Z) (elementaryPredictable 𝓕 c d Y) := by
  rw [C.inner_elementaryIntegralValue_eq_zero_of_le hab hbc hcd Z Y,
    inner_elementaryPredictable_eq_zero_of_le 𝓕 hbc Z Y]
end ClarkOconeFamily
end Malliavin
