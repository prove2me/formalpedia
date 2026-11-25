-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.hasOrder_iteratedLineDeriv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:56:37.518626+00:00
-- url     : https://prove2.me/submissions/eb4c8868-2a93-4711-b55a-aba8b91b08ed

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMultiplication
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_HasOrder_zero
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_HasOrder_comp
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_hasOrder_lineDeriv
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
theorem _root_.solution {k : ℕ} (w : Fin k → E) :
    HasOrder (iteratedLineDerivOpCLM ℂ 𝓢'(E, ℂ) w) k := by
  induction k with
  | zero =>
    have : iteratedLineDerivOpCLM ℂ 𝓢'(E, ℂ) w = ContinuousLinearMap.id ℂ _ := by
      ext1 u; simp
    rw [this]; simpa using HasOrder.id
  | succ k ih =>
    have : iteratedLineDerivOpCLM ℂ 𝓢'(E, ℂ) w =
        lineDerivOpCLM ℂ 𝓢'(E, ℂ) (w 0) ∘L iteratedLineDerivOpCLM ℂ 𝓢'(E, ℂ) (Fin.tail w) := by
      ext1 u; simp [iteratedLineDerivOp_succ_left]
    rw [this]
    have h := (hasOrder_lineDeriv (w 0)).comp (ih (Fin.tail w))
    rwa [show (1 : ℝ) + k = ((k + 1 : ℕ) : ℝ) by push_cast; ring] at h
end GroundTheory.Automorphic.Sobolev
