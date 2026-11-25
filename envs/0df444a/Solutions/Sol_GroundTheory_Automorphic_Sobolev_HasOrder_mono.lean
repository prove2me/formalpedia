-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.HasOrder.mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:19:17.795529+00:00
-- url     : https://prove2.me/submissions/19a8494c-cec8-4c02-8a9a-98008059045e

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMultiplication
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_sob_mono


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.Sobolev
open TemperedDistribution MeasureTheory FourierTransform LineDeriv
open scoped SchwartzMap ENNReal ContDiff
noncomputable section
set_option linter.unusedSectionVars false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
open GroundTheory.Automorphic.Sobolev.HasOrder
variable {T T₁ T₂ : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ)} {k k₁ k₂ : ℝ}
namespace GroundTheory.Automorphic.Sobolev.HasOrder
theorem _root_.solution (h : HasOrder T k) {k' : ℝ} (hk : k ≤ k') : HasOrder T k' := by
  intro s
  obtain ⟨C, hC0, hC⟩ := h s
  exact ⟨C, hC0, fun u hu ↦ (sob_mono (by linarith) _).trans (hC u hu)⟩
end GroundTheory.Automorphic.Sobolev.HasOrder
