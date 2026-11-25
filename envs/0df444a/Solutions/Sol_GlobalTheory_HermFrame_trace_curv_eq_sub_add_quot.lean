-- Prove2me | solution 1 for GlobalTheory.HermFrame.trace_curv_eq_sub_add_quot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:46:42.491041+00:00
-- url     : https://prove2.me/submissions/bc88b5f8-ac01-4d44-b1b4-8ff6972218ee

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ChernOneEqNegDdcLogDet
import Theorems.Thm_GlobalTheory_HermFrame_trace_curv_eq_neg_dbar
import Theorems.Thm_GlobalTheory_HermFrame_trace_conn_eq_sub_add_quot
import Theorems.Thm_GlobalTheory_HermFrame_isUnit_det_quotGram
import Theorems.Thm_GlobalTheory_dbar_add
import Theorems.Thm_GlobalTheory_dbar_congr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex ComplexConjugate Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.HermFrame
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E]
variable {m n l : Type*}
variable [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l]
  {H : E → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : E}
namespace GlobalTheory.HermFrame
theorem _root_.solution (h : MContDiffAt 2 H z) (hu : IsUnit (H z).det)
    (hs : IsUnit (subGram (H z)).det) (ξ η : E) : (curv H z ξ η).trace =
      (curv (fun x => subGram (H x)) z ξ η).trace +
        (curv (fun x => quotGram (H x)) z ξ η).trace := by
  have hq := isUnit_det_quotGram hu hs
  have he : (fun x => (conn H x ξ).trace) =ᶠ[𝓝 z] fun x =>
      (conn (fun x => subGram (H x)) x ξ).trace + (conn (fun x => quotGram (H x)) x ξ).trace := by
    filter_upwards [h.eventually_two, h.eventually_isUnit hu, h.subGram.eventually_isUnit hs]
      with x h1 h2 h3
    exact trace_conn_eq_sub_add_quot (h1.of_le one_le_two) h2 h3 ξ
  have hS : MContDiffAt 1 (fun x => conn (fun x => subGram (H x)) x ξ) z :=
    h.subGram.conn hs (by norm_num) ξ
  have hQ : MContDiffAt 1 (fun x => conn (fun x => quotGram (H x)) x ξ) z :=
    (h.quotGram hs).conn hq (by norm_num) ξ
  rw [trace_curv_eq_neg_dbar h hu, trace_curv_eq_neg_dbar h.subGram hs,
    trace_curv_eq_neg_dbar (h.quotGram hs) hq, dbar_congr he, dbar_add,
    ContinuousLinearMap.add_apply, neg_add]
  · exact DifferentiableAt.fun_sum fun a _ => hS.diff a a
  · exact DifferentiableAt.fun_sum fun a _ => hQ.diff a a
end GlobalTheory.HermFrame
