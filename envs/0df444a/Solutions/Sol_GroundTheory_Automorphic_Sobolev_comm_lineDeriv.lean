-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.comm_lineDeriv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:33:45.136981+00:00
-- url     : https://prove2.me/submissions/38ed7242-cbd1-4818-b2f8-6153378f20e4

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMultiplication
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_lineDerivOp_smulLeftCLM
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_comm_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.Sobolev
open TemperedDistribution MeasureTheory FourierTransform LineDeriv
open scoped SchwartzMap ENNReal ContDiff
noncomputable section
set_option linter.unusedSectionVars false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
namespace GroundTheory.Automorphic.Sobolev
theorem _root_.solution (v : E) (ψ : 𝓢(E, ℂ)) :
    comm (lineDerivOpCLM ℂ 𝓢'(E, ℂ) v) ψ = smulLeftCLM ℂ ((∂_{v} ψ : 𝓢(E, ℂ)) : E → ℂ) := by
  ext1 u
  rw [comm_apply, lineDerivOpCLM_apply, lineDerivOpCLM_apply, lineDerivOp_smulLeftCLM]
  abel
end GroundTheory.Automorphic.Sobolev
