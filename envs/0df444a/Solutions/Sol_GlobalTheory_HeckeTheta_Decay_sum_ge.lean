-- Prove2me | solution 1 for GlobalTheory.HeckeTheta.Decay.sum_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:20:32.922245+00:00
-- url     : https://prove2.me/submissions/050385cb-0f02-4f92-ac0f-8e4677349b74

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormWt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegrableWeightedHeckeThetaKernelHalfSpace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField MeasureTheory
noncomputable section
open GlobalTheory GlobalTheory.HeckeTheta GlobalTheory.HeckeTheta.Decay
open GlobalTheory.HeckeTheta
variable {I : Type} [Fintype I]
namespace GlobalTheory.HeckeTheta.Decay
theorem _root_.solution (y : I → ℝ) (v : I → ℂ) {τ : ℝ} (hτ : 0 ≤ τ) (hy : ∀ i, τ ≤ Real.exp (y i)) :
    τ * ‖v‖ ^ 2 ≤ ∑ i, Real.exp (y i) * ‖v i‖ ^ 2 := by
  have hv : ‖v‖ ^ 2 ≤ ∑ i, ‖v i‖ ^ 2 := by
    have : ‖v‖ ≤ Real.sqrt (∑ i, ‖v i‖ ^ 2) := by
      refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun i => ?_
      refine (le_abs_self _).trans (Real.abs_le_sqrt ?_)
      exact Finset.single_le_sum (f := fun i => ‖v i‖ ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ i)
    calc ‖v‖ ^ 2 ≤ (Real.sqrt (∑ i, ‖v i‖ ^ 2)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) this 2
      _ = _ := Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)
  calc τ * ‖v‖ ^ 2 ≤ τ * ∑ i, ‖v i‖ ^ 2 := mul_le_mul_of_nonneg_left hv hτ
    _ = ∑ i, τ * ‖v i‖ ^ 2 := Finset.mul_sum _ _ _
    _ ≤ _ := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hy i) (sq_nonneg _)
end GlobalTheory.HeckeTheta.Decay
