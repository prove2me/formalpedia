-- Prove2me | solution 1 for Malliavin.setIntegral_timeSection_eq_condExp_ae
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:56:26.238256+00:00
-- url     : https://prove2.me/submissions/b59fb12e-5606-4c92-be8c-0043293d45ea

import Definitions.Def_Malliavin_ClarkOcone
import Definitions.Def_Malliavin_WienerChaos
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.ConditionalExpectation
import Definitions.Def_Malliavin_PointwiseCondExp
import Theorems.Thm_Malliavin_setIntegral_timeSection_predictableProjection_ae
import Theorems.Thm_Malliavin_memLp_timeSection_ae


set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›)
omit [CompleteSpace W] [BorelSpace W]
namespace Malliavin
theorem _root_.solution (U : TimeProcessL2 P) {a : ℝ≥0} {A : Set W}
    (hA : MeasurableSet[𝓕 a] A) :
    ∀ᵐ t ∂nonnegativeLebesgueMeasure, a < t →
      ∫ ω in A, (predictableProjection 𝓕 U : ℝ≥0 × W → ℝ) (t, ω) ∂P
        = ∫ ω in A, (P[(fun ω ↦ U (t, ω)) | 𝓕 t]) ω ∂P := by
  filter_upwards [setIntegral_timeSection_predictableProjection_ae 𝓕 U hA,
    memLp_timeSection_ae U] with t ht hUt hat
  rw [ht hat]
  exact (setIntegral_condExp (𝓕.le t) (hUt.integrable one_le_two)
    (𝓕.mono hat.le A hA)).symm
end Malliavin
