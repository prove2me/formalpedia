-- Prove2me | solution 1 for GlobalTheory.T.fockDetCharInvariants_le_span_prodMaximalMinors
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:56:11.112865+00:00
-- url     : https://prove2.me/submissions/957f9e43-f66d-432d-b7c8-476054ccd561

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FockDetCharInvariantsLeSpanProdMaximalMinors
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdMinorsMemInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FockDetCharInvariantsLeSpanProdMaximalMinorsStatement
import Theorems.Thm_GlobalTheory_MinorFrame_inv_le_span_prodMinors


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {ι : Type} [Fintype ι] (a d : ℕ) (n : ι → ℕ), GlobalTheory.MinorFrame.inv a d n ≤ Submodule.span ℂ (Set.range (GlobalTheory.MinorFrame.prodMinors (ι := ι) (a := a) (d := d) (n := n))) := by
  first | exact @GlobalTheory.MinorFrame.inv_le_span_prodMinors | exact GlobalTheory.MinorFrame.inv_le_span_prodMinors | (intros; apply GlobalTheory.MinorFrame.inv_le_span_prodMinors <;> assumption)
end _root_.GlobalTheory.T
