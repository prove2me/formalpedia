-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.norm_ofSchwartz_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:26:47.410286+00:00
-- url     : https://prove2.me/submissions/49f6e290-cb02-47d5-924c-e11451bf76e9

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevRellich
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevEmbedding
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMultiplication
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_eLpNorm_fourier_schwartz
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_fourier_fourierMultiplierCLM_weight_apply
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_bessel_ofSchwartz


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
    ‖SobolevSpace.ofSchwartz r φ‖ =
      (eLpNorm (fun ξ ↦ weight r ξ * (𝓕 φ : 𝓢(E, ℂ)) ξ) 2 volume).toReal := by
  rw [SobolevSpace.norm_def, bessel_ofSchwartz, SchwartzMap.norm_toLp,
    ← eLpNorm_fourier_schwartz]
  congr 2
  ext ξ
  exact fourier_fourierMultiplierCLM_weight_apply r φ ξ
end GroundTheory.Automorphic.Sobolev
