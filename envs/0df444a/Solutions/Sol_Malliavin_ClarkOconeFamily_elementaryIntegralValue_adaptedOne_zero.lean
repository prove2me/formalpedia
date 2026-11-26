-- Prove2me | solution 1 for Malliavin.ClarkOconeFamily.elementaryIntegralValue_adaptedOne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:30:43.828071+00:00
-- url     : https://prove2.me/submissions/d356d498-fd38-46a8-878f-f241b2c28876

import Definitions.Def_Malliavin_TimeDerivative
import Mathlib.Probability.Process.Predictable
import Definitions.Def_Malliavin_ClarkOcone
import Theorems.Thm_Malliavin_ClarkOconeFamily_elementaryIntegralValue_adaptedOne
import Theorems.Thm_Malliavin_brownianLp_zero


set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9
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
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓕) (t : ℝ≥0) :
    C.elementaryIntegralValue (zero_le : (0 : ℝ≥0) ≤ t)
        (adaptedOne (P := P) 𝓕 0) =
      brownianLp C.isPreBrownian t := by
  rw [C.elementaryIntegralValue_adaptedOne, brownianLp_zero, sub_zero]
end ClarkOconeFamily
end Malliavin
