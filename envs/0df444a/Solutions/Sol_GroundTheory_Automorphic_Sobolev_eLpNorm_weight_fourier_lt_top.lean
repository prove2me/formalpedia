-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.eLpNorm_weight_fourier_lt_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:29:10.104051+00:00
-- url     : https://prove2.me/submissions/bd823f2c-64c5-488b-8e72-948f64d9bcdc

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevRellich
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevEmbedding
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMultiplication
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_fourier_fourierMultiplierCLM_weight_apply

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
theorem _root_.solution (r : ℝ) (φ : 𝓢(E, ℂ)) :
    eLpNorm (fun ξ ↦ weight r ξ * (𝓕 φ : 𝓢(E, ℂ)) ξ) 2 volume < (⊤ : ℝ≥0∞) := by
  have h : (fun ξ ↦ weight r ξ * (𝓕 φ : 𝓢(E, ℂ)) ξ) =
      ⇑(𝓕 (SchwartzMap.fourierMultiplierCLM ℂ (weight r) φ) : 𝓢(E, ℂ)) := by
    ext ξ; exact (fourier_fourierMultiplierCLM_weight_apply r φ ξ).symm
  rw [h]
  exact ((𝓕 (SchwartzMap.fourierMultiplierCLM ℂ (weight r) φ) : 𝓢(E, ℂ)).memLp 2 volume).eLpNorm_lt_top
end GroundTheory.Automorphic.Sobolev
