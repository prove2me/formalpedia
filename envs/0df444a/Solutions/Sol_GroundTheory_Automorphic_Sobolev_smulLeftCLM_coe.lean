-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.smulLeftCLM_coe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:54:13.760087+00:00
-- url     : https://prove2.me/submissions/51fbe26b-faf8-45d3-ab5c-8d551d3bcd8a

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevRellich
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevEmbedding
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMultiplication

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
theorem _root_.solution (χ : 𝓢(E, ℂ)) (φ : 𝓢(E, ℂ)) :
    smulLeftCLM ℂ (χ : E → ℂ) (φ : 𝓢'(E, ℂ)) =
      ((SchwartzMap.smulLeftCLM ℂ (χ : E → ℂ) φ : 𝓢(E, ℂ)) : 𝓢'(E, ℂ)) := by
  ext ψ
  rw [smulLeftCLM_apply_apply, SchwartzMap.coe_apply, SchwartzMap.coe_apply]
  congr 1; ext x
  rw [SchwartzMap.smulLeftCLM_apply_apply χ.hasTemperateGrowth,
    SchwartzMap.smulLeftCLM_apply_apply χ.hasTemperateGrowth, smul_eq_mul, smul_eq_mul,
    smul_eq_mul, smul_eq_mul]
  ring
end GroundTheory.Automorphic.Sobolev
