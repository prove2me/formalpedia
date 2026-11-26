-- Prove2me | solution 1 for Malliavin.ClarkOconeFamily.IsBrownianOnElementary.isBrownianOnDeterministic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:02:37.173168+00:00
-- url     : https://prove2.me/submissions/c017ab57-f8a0-4f36-871c-49c2c2ce8ca2

import Definitions.Def_Malliavin_TimeDerivative
import Mathlib.Probability.Process.Predictable
import Definitions.Def_Malliavin_ClarkOcone
import Theorems.Thm_Malliavin_elementaryPredictable_adaptedOne
import Theorems.Thm_Malliavin_ClarkOconeFamily_elementaryIntegralValue_adaptedOne_zero

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
namespace ClarkOconeFamily.IsBrownianOnElementary
theorem _root_.solution
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›} {C : ClarkOconeFamily B P 𝓕}
    (hC : C.IsBrownianOnElementary) : C.IsBrownianOnDeterministic := by
  intro t
  have h := hC (zero_le : (0 : ℝ≥0) ≤ t) (adaptedOne (P := P) 𝓕 0)
  rw [elementaryPredictable_adaptedOne,
    C.elementaryIntegralValue_adaptedOne_zero] at h
  exact h
end ClarkOconeFamily.IsBrownianOnElementary
end Malliavin
