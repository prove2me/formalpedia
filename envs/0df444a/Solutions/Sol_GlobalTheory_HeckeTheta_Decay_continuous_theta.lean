-- Prove2me | solution 1 for GlobalTheory.HeckeTheta.Decay.continuous_theta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:10:57.184793+00:00
-- url     : https://prove2.me/submissions/db3e6a02-16d9-47b5-b0ad-296063e43ac9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormWt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegrableWeightedHeckeThetaKernelHalfSpace
import Theorems.Thm_GlobalTheory_HeckeTheta_Decay_norm_term_le
import Theorems.Thm_GlobalTheory_HeckeTheta_Decay_continuous_hmon
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
open NumberField MeasureTheory
noncomputable section
open GlobalTheory GlobalTheory.HeckeTheta GlobalTheory.HeckeTheta.Decay
open GlobalTheory.HeckeTheta
variable {I : Type} [Fintype I]
namespace GlobalTheory.HeckeTheta.Decay
theorem _root_.solution {ι : Type} (e : ι → I → ℂ) (a : ι → ℂ) (n : I → ℤ)
    (ha : ∀ ε : ℝ, 0 < ε → Summable (fun j => ‖a j‖ * Real.exp (-ε * ‖e j‖ ^ 2))) :
    Continuous (theta e a n) := by
  rw [continuous_iff_continuousAt]
  intro y0
  obtain ⟨L, hL⟩ : ∃ L : ℝ, ∀ i, -L < y0 i := ⟨∑ i, |y0 i| + 1, fun i => by
      have := Finset.single_le_sum (f := fun i => |y0 i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i)
      have := neg_abs_le (y0 i)
      linarith⟩
  let U : Set (I → ℝ) := {y | ∀ i, -L < y i}
  have hU : IsOpen U := by
    simp only [U, Set.setOf_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_apply i)
  have hc : ContinuousOn (theta e a n) U := by
    unfold theta
    refine continuousOn_tsum
      (u := fun j => gC n * (‖a j‖ * Real.exp (-(Real.pi * Real.exp (-L)) * ‖e j‖ ^ 2)))
      (fun j => ?_) ?_ ?_
    · apply Continuous.continuousOn
      apply continuous_const.mul
      unfold gauss
      refine continuous_finset_prod _ fun i _ => ?_
      have hd : Continuous fun y : I → ℝ => dil y (e j) i := by unfold dil; fun_prop
      exact ((continuous_hmon _).comp hd).mul (by fun_prop)
    · exact (ha _ (by positivity)).mul_left _
    · intro j y hy
      rw [norm_mul]
      have h := norm_term_le n y (e j) (Real.exp_pos (-L)).le fun i => Real.exp_le_exp.mpr (hy i).le
      calc ‖a j‖ * ‖gauss n (dil y (e j))‖
          ≤ ‖a j‖ * (gC n * Real.exp (-Real.pi * Real.exp (-L) * ‖e j‖ ^ 2)) :=
            mul_le_mul_of_nonneg_left h (norm_nonneg _)
        _ = _ := by ring_nf
  exact hc.continuousAt (hU.mem_nhds hL)
end GlobalTheory.HeckeTheta.Decay
