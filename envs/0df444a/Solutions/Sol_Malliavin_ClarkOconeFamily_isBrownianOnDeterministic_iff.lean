-- Prove2me | solution 1 for Malliavin.ClarkOconeFamily.isBrownianOnDeterministic_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:02:44.831273+00:00
-- url     : https://prove2.me/submissions/1dd9be7a-00c6-4ea5-9969-1e4d7484e686

import Definitions.Def_Malliavin_TimeDerivative
import Mathlib.Probability.Process.Predictable
import Definitions.Def_Malliavin_ClarkOcone
import Theorems.Thm_Malliavin_ClarkOconeFamily_deterministicIntegral_apply
import Theorems.Thm_Malliavin_ClarkOconeFamily_IsBrownianOnDeterministic_deterministicIntegral_eq_wienerIntegral
import Theorems.Thm_Malliavin_wienerIntegral_intervalIndicator


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
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›} (C : ClarkOconeFamily B P 𝓕) :
    C.IsBrownianOnDeterministic ↔
      C.deterministicIntegral = wienerIntegral C.isPreBrownian := by
  constructor
  · exact fun hC ↦ hC.deterministicIntegral_eq_wienerIntegral
  · intro hC t
    have ht := DFunLike.congr_fun hC (intervalIndicator t)
    rw [C.deterministicIntegral_apply, wienerIntegral_intervalIndicator] at ht
    exact ht
end ClarkOconeFamily
end Malliavin
