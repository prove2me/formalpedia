-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.mulPrin_coe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:29:38.007824+00:00
-- url     : https://prove2.me/submissions/a4180273-31f3-4774-891e-2edb42ad7ad7

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevRellich
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevEmbedding
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMultiplication
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_smulLeftCLM_coe
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
open TemperedDistribution MeasureTheory FourierTransform
open scoped SchwartzMap ENNReal ContDiff
noncomputable section
set_option linter.unusedSectionVars false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable (χ : 𝓢(E, ℂ))
namespace GroundTheory.Automorphic.Sobolev
theorem _root_.solution (χ : 𝓢(E, ℂ)) (r : ℝ) (φ : 𝓢(E, ℂ)) :
    mulPrin χ r (φ : 𝓢'(E, ℂ)) =
      ((SchwartzMap.fourierMultiplierCLM ℂ (weight (-r)) (SchwartzMap.smulLeftCLM ℂ (χ : E → ℂ)
        (SchwartzMap.fourierMultiplierCLM ℂ (weight r) φ)) : 𝓢(E, ℂ)) : 𝓢'(E, ℂ)) := by
  simp only [mulPrin, ContinuousLinearMap.comp_apply]
  rw [fourierMultiplierCLM_toTemperedDistributionCLM_eq (weight_hasTemperateGrowth r),
    smulLeftCLM_coe, fourierMultiplierCLM_toTemperedDistributionCLM_eq (weight_hasTemperateGrowth _)]
end GroundTheory.Automorphic.Sobolev
