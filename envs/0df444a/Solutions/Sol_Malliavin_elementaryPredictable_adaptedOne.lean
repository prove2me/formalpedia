-- Prove2me | solution 1 for Malliavin.elementaryPredictable_adaptedOne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:29:45.355844+00:00
-- url     : https://prove2.me/submissions/52fd3a6c-c707-4bfa-94fe-274184593f23

import Definitions.Def_Malliavin_TimeDerivative
import Mathlib.Probability.Process.Predictable
import Definitions.Def_Malliavin_ClarkOcone
import Theorems.Thm_Malliavin_deterministicPredictableEmbedding_coeFn
import Theorems.Thm_Malliavin_elementaryPredictable_coeLp

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
omit [CompleteSpace W] [BorelSpace W]
namespace Malliavin
theorem _root_.solution
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (t : ℝ≥0) :
    elementaryPredictable (P := P) 𝓕 0 t (adaptedOne (P := P) 𝓕 0) =
      deterministicPredictableEmbedding 𝓕 (intervalIndicator t) := by
  apply Subtype.ext
  rw [elementaryPredictable_coeLp]
  apply Lp.ext
  have hOne : ∀ᵐ p : ℝ≥0 × W ∂nonnegativeLebesgueMeasure.prod P,
      (adaptedOne (P := P) 𝓕 0 : W → ℝ) p.2 = 1 :=
    Measure.quasiMeasurePreserving_snd.ae_eq_comp (Lp.coeFn_const 2 P (1 : ℝ))
  filter_upwards [coeFn_tensor (iocIndicator 0 t)
      (adaptedOne (P := P) 𝓕 0 : RandomL2 P),
    hOne, deterministicPredictableEmbedding_coeFn 𝓕 (intervalIndicator t)]
      with p hp hOnep hdet
  rw [hp, hOnep, hdet, Function.comp_apply, mul_one]
  rfl
end Malliavin
