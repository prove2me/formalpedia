-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.fourier_fourierMultiplierCLM_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:00:22.451679+00:00
-- url     : https://prove2.me/submissions/d46a56f0-5398-4a22-8a28-6e4aea1b3682

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_Sobolev
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevDuality
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMollifier

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
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {m : E → ℂ} {C s t : ℝ}
namespace GroundTheory.Automorphic.Sobolev
theorem _root_.solution (m : E → ℂ) (u : 𝓢'(E, F)) (φ : 𝓢(E, ℂ)) :
    𝓕 (fourierMultiplierCLM F m u) φ = 𝓕 u (SchwartzMap.smulLeftCLM ℂ m φ) := by
  rw [fourierMultiplierCLM_apply, FourierTransform.fourier_fourierInv_eq, smulLeftCLM_apply_apply]
end GroundTheory.Automorphic.Sobolev
