-- Prove2me | solution 1 for GlobalTheory.HermFrame.trace_conn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:00:27.724166+00:00
-- url     : https://prove2.me/submissions/a4f550b6-f965-47a9-9681-66a04068fe77

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ChernOneEqNegDdcLogDet
import Theorems.Thm_GlobalTheory_HermFrame_del_det

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
variable [Fintype n] [DecidableEq n] {H : E → Matrix n n ℂ} {z : E}
namespace GlobalTheory.HermFrame
theorem _root_.solution (h : MContDiffAt 1 H z) (hu : IsUnit (H z).det) (ξ : E) :
    (conn H z ξ).trace = (H z).det⁻¹ * del (fun x => (H x).det) z ξ := by
  have _ := hu
  rw [del_det h, conn, ← transpose_nonsing_inv, ← transpose_mul, trace_transpose, trace_mul_comm,
    Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_mul, trace_smul, smul_eq_mul]
end GlobalTheory.HermFrame
