-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.hasOrder_comm_prinOp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:03:51.486804+00:00
-- url     : https://prove2.me/submissions/3b283108-c38a-4112-9e62-9d8054e49208

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMultiplication
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_HasOrder_comp
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_HasOrder_sum
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_hasOrder_smulLeft
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_IsLocal_comp
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_IsLocal_sum
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_comm_smulLeft_comp
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_comm_sum
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_hasOrder_comm_iteratedLineDeriv
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
variable {ι : Type*} [Fintype ι] {m : ℕ} (a : ι → 𝓢(E, ℂ)) (w : ι → Fin m → E)
namespace GroundTheory.Automorphic.Sobolev
theorem _root_.solution (ψ : 𝓢(E, ℂ)) : HasOrder (comm (prinOp a w) ψ) ((m : ℝ) - 1) := by
  rw [prinOp, comm_sum]
  refine HasOrder.sum _ fun i _ ↦ ?_
  rw [comm_smulLeft_comp (a i).hasTemperateGrowth]
  simpa using (hasOrder_smulLeft (a i)).comp (hasOrder_comm_iteratedLineDeriv (w i) ψ)
end GroundTheory.Automorphic.Sobolev
