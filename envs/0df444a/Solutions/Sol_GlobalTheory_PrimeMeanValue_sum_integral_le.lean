-- Prove2me | solution 1 for GlobalTheory.PrimeMeanValue.sum_integral_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:30:56.914821+00:00
-- url     : https://prove2.me/submissions/fb8ab1b7-6cfd-4c5c-8c42-c4515a99671e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IntegralNormSqLp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_BrunTitchmarshExistsConstStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_PrimeMeanValueCharactersTwistIntegralLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
open GlobalTheory GlobalTheory.PrimeMeanValue
namespace GlobalTheory.PrimeMeanValue
theorem _root_.solution {ι : Type*} (s : Finset ι) (μ : Measure ℝ) (f : ι → ℝ → ℝ) (G : ℝ → ℝ)
    (hm : ∀ i, AEStronglyMeasurable (f i) μ) (h0 : ∀ᵐ x ∂μ, ∀ i, 0 ≤ f i x)
    (hG : Integrable G μ) (h : ∀ᵐ x ∂μ, ∑ i ∈ s, f i x ≤ G x) :
    ∑ i ∈ s, ∫ x, f i x ∂μ ≤ ∫ x, G x ∂μ := by
  have hi : ∀ i ∈ s, Integrable (f i) μ := fun i hi => by
    refine hG.mono' (hm i) ?_
    filter_upwards [h0, h] with x hx0 hx
    rw [Real.norm_of_nonneg (hx0 i)]
    exact (Finset.single_le_sum (f := fun i => f i x) (fun j _ => hx0 j) hi).trans hx
  rw [← integral_finsetSum s hi]
  exact integral_mono_ae (integrable_finsetSum s hi) hG h
end GlobalTheory.PrimeMeanValue
