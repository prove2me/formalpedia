-- Prove2me | solution 1 for GlobalTheory.PoincareBounds.norm_mul_tlog_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:54:25.68059+00:00
-- url     : https://prove2.me/submissions/9304fc27-a66d-47f4-afa7-b2b0c23ece15

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_HodgePeriodGram
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PoincareMetricPuncturedPolydiscBounds
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_HodgePeriodGram_tlog_pos


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram GlobalTheory.HermFrame
noncomputable section
open GlobalTheory GlobalTheory.PoincareBounds
namespace GlobalTheory.PoincareBounds
theorem _root_.solution {w : ℂ} (h0 : w ≠ 0) (h1 : ‖w‖ < 1) :
    0 < ‖w‖ * tlog w ∧ ‖w‖ * tlog w < 1 := by
  have hx : 0 < ‖w‖ := norm_pos_iff.2 h0
  refine ⟨mul_pos hx (tlog_pos h0 h1), ?_⟩
  have hl := Real.abs_log_mul_self_lt ‖w‖ hx h1.le
  have hpi : 1 < 2 * Real.pi := by linarith [Real.pi_gt_three]
  have e : ‖w‖ * tlog w = -(Real.log ‖w‖ * ‖w‖) / (2 * Real.pi) := by
    unfold tlog; ring
  rw [e, div_lt_one (by linarith)]
  have := neg_le_abs (Real.log ‖w‖ * ‖w‖)
  linarith
end GlobalTheory.PoincareBounds
