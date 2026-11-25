-- Prove2me | solution 1 for GlobalTheory.MinorFrame.RowIrr.topMinors_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:13:54.674925+00:00
-- url     : https://prove2.me/submissions/892be86d-18cc-4ad7-b88a-e9ba2a8485c7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdMinorsMemInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EvalBasePtTopMinors
import Theorems.Thm_GlobalTheory_MinorFrame_RowIrr_eval_basePt_topMinors

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open GlobalTheory GlobalTheory.MinorFrame GlobalTheory.MinorFrame.RowIrr
open GlobalTheory.MinorFrame
variable {ι : Type} [Fintype ι]
namespace GlobalTheory.MinorFrame.RowIrr
theorem _root_.solution {a d : ℕ} (h : a ≤ d) (n : ι → ℕ) : topMinors (ι := ι) h n ≠ 0 := by
  intro h0
  have := eval_basePt_topMinors (ι := ι) h n
  rw [h0, map_zero] at this
  exact zero_ne_one this
end GlobalTheory.MinorFrame.RowIrr
