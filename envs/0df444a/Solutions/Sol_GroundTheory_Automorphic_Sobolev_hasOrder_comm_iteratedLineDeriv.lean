-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.hasOrder_comm_iteratedLineDeriv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:34:33.186715+00:00
-- url     : https://prove2.me/submissions/0f3ff978-e459-4ea7-b687-ed891fa957c4

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMultiplication
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_HasOrder_mono
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_HasOrder_add
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_HasOrder_zero
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_HasOrder_comp
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_hasOrder_smulLeft
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_hasOrder_lineDeriv
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_hasOrder_iteratedLineDeriv
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_IsLocal_add
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_IsLocal_comp
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_IsLocal_zero
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_comm_apply
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_comm_lineDeriv
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_comm_comp
import Theorems.Thm_GroundTheory_Automorphic_IsHilbertSchmidt_add
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
theorem _root_.solution {k : ℕ} (w : Fin k → E) (ψ : 𝓢(E, ℂ)) :
    HasOrder (comm (iteratedLineDerivOpCLM ℂ 𝓢'(E, ℂ) w) ψ) (k - 1) := by
  induction k with
  | zero =>
    have : comm (iteratedLineDerivOpCLM ℂ 𝓢'(E, ℂ) w) ψ = 0 := by
      ext1 u; simp [comm_apply]
    rw [this]; exact HasOrder.zero _
  | succ k ih =>
    have e : iteratedLineDerivOpCLM ℂ 𝓢'(E, ℂ) w =
        lineDerivOpCLM ℂ 𝓢'(E, ℂ) (w 0) ∘L iteratedLineDerivOpCLM ℂ 𝓢'(E, ℂ) (Fin.tail w) := by
      ext1 u; simp [iteratedLineDerivOp_succ_left]
    rw [e, comm_comp, comm_lineDeriv]
    have h1 := (hasOrder_lineDeriv (E := E) (w 0)).comp (ih (Fin.tail w))
    have h2 := (hasOrder_smulLeft (∂_{w 0} ψ : 𝓢(E, ℂ))).comp
      (hasOrder_iteratedLineDeriv (E := E) (Fin.tail w))
    refine (h1.mono (le_of_eq ?_)).add (h2.mono (le_of_eq ?_)) <;> push_cast <;> ring
end GroundTheory.Automorphic.Sobolev
