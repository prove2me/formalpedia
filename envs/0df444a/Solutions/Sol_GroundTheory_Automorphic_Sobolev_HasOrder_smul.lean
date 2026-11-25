-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.HasOrder.smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:54:03.777742+00:00
-- url     : https://prove2.me/submissions/ab8807e9-ff2e-435f-968e-489e3056c835

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMultiplication
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_sob_smul_le


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
theorem _root_.solution (h : HasOrder T k) (c : ℂ) : HasOrder (c • T) k := by
  intro s
  obtain ⟨C, hC0, hC⟩ := h s
  refine ⟨‖c‖ * C, by positivity, fun u hu ↦ ?_⟩
  rw [smul_apply, ENNReal.ofReal_mul (norm_nonneg c), ofReal_norm, mul_assoc]
  exact (sob_smul_le _ _).trans (mul_le_mul_right (hC u hu) _)
end GroundTheory.Automorphic.Sobolev.HasOrder
