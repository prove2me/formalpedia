-- Prove2me | solution 1 for GlobalTheory.JR.Step.delta_lift_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:39:57.587794+00:00
-- url     : https://prove2.me/submissions/a612806d-d461-4c34-80c5-c1d006483911

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullToGlIsSelfAdjoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisBorderedMatrixNormalFormInvariantsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisHankelDetNeZeroOfLift
import Theorems.Thm_GlobalTheory_JR_DeltaLift_det_Bm_lift
import Theorems.Thm_GlobalTheory_JR_DeltaLift_det_Cm_lift
import Theorems.Thm_GlobalTheory_T_jacquetRallis_borderedMatrix_normalForm_invariants


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory.JR.DeltaLift
namespace GlobalTheory.JR.Step
theorem _root_.solution : ∀ (k : Type) [Field k] (r : ℕ) (Z : Gl r k) (μ l : k),
    Delta (inv (GlobalTheory.JR.Step.lift Z μ l)) ≠ 0 → Delta (inv Z) ≠ 0 := by
  intro k _ r Z μ l h
  have e1 := (GlobalTheory.T.jacquetRallis_borderedMatrix_normalForm_invariants k (r + 1)).2.2.1 (GlobalTheory.JR.Step.lift Z μ l)
  have e0 := (GlobalTheory.T.jacquetRallis_borderedMatrix_normalForm_invariants k r).2.2.1 Z
  unfold Delta at h ⊢
  rw [← e1, det_mul] at h
  rw [← e0, det_mul]
  have hC : (Cm (GlobalTheory.JR.Step.lift Z μ l)).det ≠ 0 := left_ne_zero_of_mul h
  have hB : (Bm (GlobalTheory.JR.Step.lift Z μ l)).det ≠ 0 := right_ne_zero_of_mul h
  exact mul_ne_zero (fun hc => hC (det_Cm_lift Z μ l hc)) (fun hb => hB (det_Bm_lift Z μ l hb))
end GlobalTheory.JR.Step
