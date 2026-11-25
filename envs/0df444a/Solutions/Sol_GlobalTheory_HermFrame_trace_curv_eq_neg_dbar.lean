-- Prove2me | solution 1 for GlobalTheory.HermFrame.trace_curv_eq_neg_dbar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:47:10.286862+00:00
-- url     : https://prove2.me/submissions/8caaa2d5-e020-4519-b0cd-f90e45ec2d33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ChernOneEqNegDdcLogDet
import Theorems.Thm_GlobalTheory_HermFrame_opNorm_zero
import Theorems.Thm_GlobalTheory_dbar_sum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.HermFrame.opNorm_zero



set_option autoImplicit false
open Matrix Complex ComplexConjugate Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.HermFrame
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E]
variable {m n l : Type*}
variable [Fintype n] [DecidableEq n] {H : E → Matrix n n ℂ} {z : E}
namespace GlobalTheory.HermFrame
theorem _root_.solution (h : MContDiffAt 2 H z) (hu : IsUnit (H z).det) (ξ η : E) :
    (curv H z ξ η).trace = -dbar (fun x => (conn H x ξ).trace) z η := by
  have hc : MContDiffAt 1 (fun x => conn H x ξ) z := h.conn hu (by norm_num) ξ
  simp only [curv, trace, diag_apply, Matrix.neg_apply, mdbar_apply, Finset.sum_neg_distrib]
  rw [dbar_sum fun a _ => hc.diff a a, ContinuousLinearMap.sum_apply]
end GlobalTheory.HermFrame
