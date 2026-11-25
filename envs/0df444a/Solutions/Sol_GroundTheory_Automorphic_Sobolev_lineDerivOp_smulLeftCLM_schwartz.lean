-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.lineDerivOp_smulLeftCLM_schwartz
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:22:20.596427+00:00
-- url     : https://prove2.me/submissions/49948c5c-c0c8-485f-b047-606d3acb37e4

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMultiplication
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators
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
theorem _root_.solution (v : E) (ψ φ : 𝓢(E, ℂ)) :
    ∂_{v} (SchwartzMap.smulLeftCLM ℂ (ψ : E → ℂ) φ) =
      SchwartzMap.smulLeftCLM ℂ ((∂_{v} ψ : 𝓢(E, ℂ)) : E → ℂ) φ +
        SchwartzMap.smulLeftCLM ℂ (ψ : E → ℂ) (∂_{v} φ) := by
  ext x
  have hψ := ψ.hasTemperateGrowth
  have hψ' := (∂_{v} ψ : 𝓢(E, ℂ)).hasTemperateGrowth
  rw [add_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv,
    SchwartzMap.smulLeftCLM_apply_apply hψ', SchwartzMap.smulLeftCLM_apply_apply hψ,
    SchwartzMap.lineDerivOp_apply_eq_fderiv, SchwartzMap.lineDerivOp_apply_eq_fderiv]
  have e : ⇑(SchwartzMap.smulLeftCLM ℂ (ψ : E → ℂ) φ) = fun y ↦ ψ y * φ y := by
    ext y; rw [SchwartzMap.smulLeftCLM_apply_apply hψ, smul_eq_mul]
  rw [e, fderiv_fun_mul (ψ.differentiableAt) (φ.differentiableAt)]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring
end GroundTheory.Automorphic.Sobolev
