-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.iteratedLineDeriv_eq_fourierMultiplier
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:07:29.198817+00:00
-- url     : https://prove2.me/submissions/62074652-33c2-4f06-9ca3-1c98f6353e35

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMultiplication
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_HasOrder_zero
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_IsLocal_zero
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_derivSymb_succ
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_derivSymb_hasTemperateGrowth
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
theorem _root_.solution {k : ℕ} (w : Fin k → E) (u : 𝓢'(E, ℂ)) :
    ∂^{w} u = fourierMultiplierCLM ℂ (derivSymb w) u := by
  induction k generalizing u with
  | zero =>
    have : derivSymb w = fun _ ↦ 1 := by ext ξ; simp [derivSymb]
    rw [this, fourierMultiplierCLM_const]; simp
  | succ k ih =>
    have hg : (fun x : E ↦ ((inner ℝ x (w 0) : ℝ) : ℂ)).HasTemperateGrowth := by fun_prop
    rw [iteratedLineDerivOp_succ_left, ih, lineDeriv_eq_fourierMultiplierCLM,
      fourierMultiplierCLM_fourierMultiplierCLM_apply (derivSymb_hasTemperateGrowth _) hg,
      ← smul_apply, ← fourierMultiplierCLM_smul ((derivSymb_hasTemperateGrowth _).mul hg)]
    congr 2
    ext ξ
    simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
    rw [derivSymb_succ]; ring
end GroundTheory.Automorphic.Sobolev
