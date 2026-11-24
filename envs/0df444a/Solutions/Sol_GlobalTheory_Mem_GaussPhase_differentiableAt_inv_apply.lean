-- Prove2me | solution 1 for GlobalTheory.Mem.GaussPhase.differentiableAt_inv_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:55:47.027322+00:00
-- url     : https://prove2.me/submissions/9245fb5a-62dc-49ec-a4f1-18bb36fcdf8b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DifferentiableAtDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DifferentiableAtInvApply
import Theorems.Thm_GlobalTheory_Mem_GaussPhase_differentiableAt_det
import Theorems.Thm_GlobalTheory_DifferentiableDet_differentiableAt_det


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexOrder
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.GaussPhase
variable {σ : Type} [Fintype σ] [DecidableEq σ]
namespace GlobalTheory.Mem.GaussPhase
theorem _root_.solution (M : ℝ → Matrix σ σ ℂ) (t : ℝ)
    (hM : ∀ i j, DifferentiableAt ℝ (fun s => M s i j) t) (hne : (M t).det ≠ 0) (i j : σ) :
    DifferentiableAt ℝ (fun s => (M s)⁻¹ i j) t := by
  have hadj : DifferentiableAt ℝ (fun s => (M s).adjugate i j) t := by
    have := differentiableAt_det (fun s => (M s).updateRow j (Pi.single i 1)) t (by
      intro a b
      by_cases h : a = j
      · simp only [updateRow_apply, h, if_true]
        exact differentiableAt_const _
      · simp only [updateRow_apply, h, if_false]
        exact hM a b)
    simpa only [adjugate_apply] using this
  have := ((differentiableAt_det M t hM).fun_inv hne).mul hadj
  refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  simp [Matrix.inv_def, Ring.inverse_eq_inv']
end GlobalTheory.Mem.GaussPhase
