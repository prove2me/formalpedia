-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.smulLeftCLM_schwartz_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:56:17.324363+00:00
-- url     : https://prove2.me/submissions/4e455dde-d4c3-4a88-84cf-28f47c8eb031

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticLocal
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_toDistribution_convolutionCLM
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_toDistribution_lineDerivCLM
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_toDistribution_sub
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.Sobolev.SobolevSpace.toDistribution_convolutionCLM
attribute [local simp] GroundTheory.Automorphic.Sobolev.SobolevSpace.toDistribution_lineDerivCLM
attribute [local simp] GroundTheory.Automorphic.Sobolev.SobolevSpace.toDistribution_sub
attribute [local simp] GroundTheory.Automorphic.Sobolev.dualEquiv_apply



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.Sobolev
open TemperedDistribution MeasureTheory FourierTransform LineDeriv
open scoped SchwartzMap ENNReal ContDiff
noncomputable section
set_option linter.unusedSectionVars false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
namespace GroundTheory.Automorphic.Sobolev
theorem _root_.solution (χ f : 𝓢(E, ℂ)) (v : 𝓢'(E, ℂ)) :
    smulLeftCLM ℂ ((SchwartzMap.smulLeftCLM ℂ (χ : E → ℂ) f : 𝓢(E, ℂ)) : E → ℂ) v =
      smulLeftCLM ℂ (χ : E → ℂ) (smulLeftCLM ℂ (f : E → ℂ) v) := by
  ext φ
  simp only [smulLeftCLM_apply_apply]
  congr 1; ext x
  simp only [SchwartzMap.smulLeftCLM_apply_apply χ.hasTemperateGrowth,
    SchwartzMap.smulLeftCLM_apply_apply f.hasTemperateGrowth,
    SchwartzMap.smulLeftCLM_apply_apply (SchwartzMap.smulLeftCLM ℂ (χ : E → ℂ) f).hasTemperateGrowth,
    smul_eq_mul]
  ring
end GroundTheory.Automorphic.Sobolev
