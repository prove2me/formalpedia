-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.lintegral_wK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:24:45.321435+00:00
-- url     : https://prove2.me/submissions/04764e0a-7a76-4e4c-893f-34f1ae7c009f

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevRellich
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevEmbedding
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMultiplication
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_integrable_wK

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.Sobolev
open TemperedDistribution MeasureTheory FourierTransform
open scoped SchwartzMap ENNReal ContDiff
noncomputable section
set_option linter.unusedSectionVars false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
namespace GroundTheory.Automorphic.Sobolev
theorem _root_.solution (c : ℝ) (ψ : 𝓢(E, ℂ)) : ∫⁻ ζ, wK c ψ ζ = ENNReal.ofReal (wInt c ψ) := by
  rw [wInt, ofReal_integral_eq_lintegral_ofReal (integrable_wK c ψ)
    (ae_of_all _ fun ζ ↦ by positivity)]
  rfl
end GroundTheory.Automorphic.Sobolev
