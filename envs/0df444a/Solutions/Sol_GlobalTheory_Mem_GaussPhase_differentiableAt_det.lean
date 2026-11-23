-- Prove2me | solution 1 for GlobalTheory.Mem.GaussPhase.differentiableAt_det
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:54:25.666595+00:00
-- url     : https://prove2.me/submissions/a7f582ca-421e-43e2-988c-e2de2ba331d7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DifferentiableAtDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DifferentiableAtInvApply
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
    (hM : ∀ i j, DifferentiableAt ℝ (fun s => M s i j) t) :
    DifferentiableAt ℝ (fun s => (M s).det) t := by
  first
  | exact @_root_.GlobalTheory.DifferentiableDet.differentiableAt_det
  | exact _root_.GlobalTheory.DifferentiableDet.differentiableAt_det
  | (apply _root_.GlobalTheory.DifferentiableDet.differentiableAt_det <;> assumption)
  | (intros; apply _root_.GlobalTheory.DifferentiableDet.differentiableAt_det <;> assumption)
  | (intros; apply @_root_.GlobalTheory.DifferentiableDet.differentiableAt_det <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.DifferentiableDet.differentiableAt_det ..)
end GlobalTheory.Mem.GaussPhase
