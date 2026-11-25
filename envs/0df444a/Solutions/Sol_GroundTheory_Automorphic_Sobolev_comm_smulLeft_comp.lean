-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.comm_smulLeft_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:48:34.410907+00:00
-- url     : https://prove2.me/submissions/4bb8d752-3982-40a4-b62a-fb0e5b099de6

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMultiplication
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_comm_apply
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
theorem _root_.solution {g : E → ℂ} (hg : g.HasTemperateGrowth) (A : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ))
    (ψ : 𝓢(E, ℂ)) : comm (smulLeftCLM ℂ g ∘L A) ψ = smulLeftCLM ℂ g ∘L comm A ψ := by
  ext1 u
  simp only [comm_apply, ContinuousLinearMap.comp_apply, map_sub]
  rw [smulLeftCLM_smulLeftCLM_apply ψ.hasTemperateGrowth hg,
    smulLeftCLM_smulLeftCLM_apply hg ψ.hasTemperateGrowth, mul_comm]
end GroundTheory.Automorphic.Sobolev
