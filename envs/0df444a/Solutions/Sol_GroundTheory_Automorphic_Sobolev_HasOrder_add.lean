-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.HasOrder.add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:19:09.289733+00:00
-- url     : https://prove2.me/submissions/553ebe62-af1e-4d71-9c06-129ef478ef2d

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMultiplication
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_sob_add_le


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
theorem _root_.solution (h₁ : HasOrder T₁ k) (h₂ : HasOrder T₂ k) : HasOrder (T₁ + T₂) k := by
  intro s
  obtain ⟨C₁, hC₁0, hC₁⟩ := h₁ s
  obtain ⟨C₂, hC₂0, hC₂⟩ := h₂ s
  refine ⟨C₁ + C₂, by positivity, fun u hu ↦ ?_⟩
  rw [add_apply, ENNReal.ofReal_add hC₁0 hC₂0, add_mul]
  exact (sob_add_le _ _).trans (add_le_add (hC₁ u hu) (hC₂ u hu))
end GroundTheory.Automorphic.Sobolev.HasOrder
