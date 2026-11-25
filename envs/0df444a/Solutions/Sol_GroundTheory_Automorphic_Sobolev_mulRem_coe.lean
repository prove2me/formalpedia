-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.mulRem_coe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:21:54.921929+00:00
-- url     : https://prove2.me/submissions/56045b2a-293f-477b-8b38-8a042f4aab81

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevRellich
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevEmbedding
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMultiplication
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_smulLeftCLM_coe
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_mulPrin_coe

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
variable (χ : 𝓢(E, ℂ))
namespace GroundTheory.Automorphic.Sobolev
theorem _root_.solution (χ : 𝓢(E, ℂ)) (r : ℝ) (φ : 𝓢(E, ℂ)) :
    mulRem χ r (φ : 𝓢'(E, ℂ)) = ((commRem χ r φ : 𝓢(E, ℂ)) : 𝓢'(E, ℂ)) := by
  rw [mulRem, sub_apply, mulPrin_coe, smulLeftCLM_coe, commRem, map_sub]
end GroundTheory.Automorphic.Sobolev
