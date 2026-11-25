-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.lineDerivOp_smulLeftCLM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:58:58.231837+00:00
-- url     : https://prove2.me/submissions/3f8c2b38-6d5f-44b4-af71-83c96d690f99

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMultiplication
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_lineDerivOp_smulLeftCLM_schwartz
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
theorem _root_.solution (v : E) (ψ : 𝓢(E, ℂ)) (u : 𝓢'(E, ℂ)) :
    ∂_{v} (smulLeftCLM ℂ (ψ : E → ℂ) u) =
      smulLeftCLM ℂ ((∂_{v} ψ : 𝓢(E, ℂ)) : E → ℂ) u + smulLeftCLM ℂ (ψ : E → ℂ) (∂_{v} u) := by
  ext φ
  simp only [lineDerivOp_apply_apply, smulLeftCLM_apply_apply, add_apply, map_neg]
  rw [lineDerivOp_smulLeftCLM_schwartz, map_add]
  ring
end GroundTheory.Automorphic.Sobolev
