-- Prove2me | solution 1 for GlobalTheory.HermFrame.trace_curv_eq_curv_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:06:37.838797+00:00
-- url     : https://prove2.me/submissions/bd36507e-375b-4ed3-b3c5-d3464377708e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ChernOneEqNegDdcLogDet
import Theorems.Thm_GlobalTheory_HermFrame_trace_conn
import Theorems.Thm_GlobalTheory_HermFrame_trace_curv_eq_neg_dbar
import Theorems.Thm_GlobalTheory_HermFrame_opNorm_zero
import Theorems.Thm_GlobalTheory_dbar_congr
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
    (curv H z ξ η).trace =
      curv (fun x => (of fun _ _ => (H x).det : Matrix Unit Unit ℂ)) z ξ η () () := by
  have he : (fun x => (conn H x ξ).trace) =ᶠ[𝓝 z]
      fun x => conn (fun x => (of fun _ _ => (H x).det : Matrix Unit Unit ℂ)) x ξ () () := by
    filter_upwards [h.eventually_two, h.eventually_isUnit hu] with x h1 h2
    rw [trace_conn (h1.of_le one_le_two) h2]
    simp [conn, Matrix.mul_apply]
  rw [trace_curv_eq_neg_dbar h hu, dbar_congr he]
  rfl
end GlobalTheory.HermFrame
