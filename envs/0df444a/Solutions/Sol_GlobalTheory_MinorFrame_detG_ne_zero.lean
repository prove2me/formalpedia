-- Prove2me | solution 1 for GlobalTheory.MinorFrame.detG_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:06:15.343128+00:00
-- url     : https://prove2.me/submissions/e1d8d90a-d8d6-4878-8644-ced94d6ac1d5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdMinorsMemInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DetGNeZero
import Theorems.Thm_GlobalTheory_MinorFrame_eval_detG
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open MvPolynomial
open GlobalTheory GlobalTheory.MinorFrame
variable {ι : Type}
namespace GlobalTheory.MinorFrame
theorem _root_.solution [Fintype ι] (a : ℕ) (n : ι → ℕ) : detG (ι := ι) a n ≠ 0 := by
  intro h
  have := eval_detG (ι := ι) a n (fun _ => 1)
  rw [h, map_zero] at this
  simp [detChar] at this
end GlobalTheory.MinorFrame
