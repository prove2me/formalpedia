-- Prove2me | solution 1 for Malliavin.ClarkOconeFamily.IsBrownianOnDeterministic.deterministicIntegral_eq_wienerIntegral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:15:27.612394+00:00
-- url     : https://prove2.me/submissions/124ad584-2dd0-43bf-a441-6f74445c219e

import Definitions.Def_Malliavin_TimeDerivative
import Mathlib.Probability.Process.Predictable
import Definitions.Def_Malliavin_ClarkOcone
import Theorems.Thm_Malliavin_ClarkOconeFamily_deterministicIntegral_apply
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
namespace ClarkOconeFamily.IsBrownianOnDeterministic
theorem _root_.solution
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›} {C : ClarkOconeFamily B P 𝓕}
    (hC : C.IsBrownianOnDeterministic) :
    C.deterministicIntegral = wienerIntegral C.isPreBrownian := by
  apply ContinuousLinearMap.ext_on dense_span_intervalIndicator
  intro f hf
  obtain ⟨t, rfl⟩ := hf
  rw [C.deterministicIntegral_apply, wienerIntegral_intervalIndicator]
  exact hC t
end ClarkOconeFamily.IsBrownianOnDeterministic
end Malliavin
