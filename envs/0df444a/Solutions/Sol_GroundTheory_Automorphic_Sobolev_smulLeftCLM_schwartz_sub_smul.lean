-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.smulLeftCLM_schwartz_sub_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:56:20.200214+00:00
-- url     : https://prove2.me/submissions/4452974d-c2b7-4900-98be-4e6fd27809a0

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
theorem _root_.solution (f g : 𝓢(E, ℂ)) (c : ℂ) (v : 𝓢'(E, ℂ)) :
    smulLeftCLM ℂ ((f - c • g : 𝓢(E, ℂ)) : E → ℂ) v =
      smulLeftCLM ℂ (f : E → ℂ) v - c • smulLeftCLM ℂ (g : E → ℂ) v := by
  ext φ
  simp only [smulLeftCLM_apply_apply, sub_apply, smul_apply]
  rw [← map_smul, ← map_sub]
  congr 1; ext x
  simp only [SchwartzMap.smulLeftCLM_apply_apply f.hasTemperateGrowth,
    SchwartzMap.smulLeftCLM_apply_apply g.hasTemperateGrowth,
    SchwartzMap.smulLeftCLM_apply_apply (f - c • g).hasTemperateGrowth, smul_eq_mul,
    sub_apply, smul_apply]
  ring
end GroundTheory.Automorphic.Sobolev
