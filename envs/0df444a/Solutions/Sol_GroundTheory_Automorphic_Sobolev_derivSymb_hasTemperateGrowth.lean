-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.derivSymb_hasTemperateGrowth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:55:24.240451+00:00
-- url     : https://prove2.me/submissions/61357a05-4501-47f5-b97d-4d32c7ee1103

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMultiplication
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_HasOrder_zero
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_IsLocal_zero
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_derivSymb_succ
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
theorem _root_.solution {k : ℕ} (w : Fin k → E) : (derivSymb w).HasTemperateGrowth := by
  induction k with
  | zero =>
    have : derivSymb w = fun _ ↦ 1 := by ext ξ; simp [derivSymb]
    rw [this]; exact Function.HasTemperateGrowth.const 1
  | succ k ih =>
    have : derivSymb w = fun ξ ↦ derivSymb (Fin.tail w) ξ *
        ((2 * Real.pi * Complex.I) * ((inner ℝ ξ (w 0) : ℝ) : ℂ)) := by
      ext ξ; exact derivSymb_succ w ξ
    rw [this]
    exact (ih _).mul (by fun_prop)
end GroundTheory.Automorphic.Sobolev
