-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.HasOrder.comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:58:52.665213+00:00
-- url     : https://prove2.me/submissions/30729c90-d1ea-45ee-addf-a9137b95ed7e

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMultiplication
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_HasOrder_memSobolev
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_sob_congr


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
theorem _root_.solution (h₁ : HasOrder T₁ k₁) (h₂ : HasOrder T₂ k₂) : HasOrder (T₁ ∘L T₂) (k₁ + k₂) := by
  intro s
  obtain ⟨C₂, hC₂0, hC₂⟩ := h₂ s
  obtain ⟨C₁, hC₁0, hC₁⟩ := h₁ (s - k₂)
  refine ⟨C₁ * C₂, by positivity, fun u hu ↦ ?_⟩
  have hmem := h₂.memSobolev hu
  rw [ContinuousLinearMap.comp_apply, sob_congr (show s - (k₁ + k₂) = s - k₂ - k₁ by ring),
    ENNReal.ofReal_mul hC₁0, mul_assoc]
  exact (hC₁ _ hmem).trans (mul_le_mul_right (hC₂ u hu) _)
end GroundTheory.Automorphic.Sobolev.HasOrder
