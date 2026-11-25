-- Prove2me | solution 1 for GlobalTheory.T.isOfFinOrder_pic_of_isReduced_finite_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:23:22.380135+00:00
-- url     : https://prove2.me/submissions/5c9d3d05-98d3-415b-9cc7-2ddb49185ff8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOfFinOrderPicOfIsReducedFiniteInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOfFinOrderPicOfIsReducedFiniteIntStatement
import Theorems.Thm_GlobalTheory_PicReducedTors_pic_isOfFinOrder


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (B : Type) [CommRing B] [IsReduced B] [Module.Finite ℤ B] (M : CommRing.Pic B), IsOfFinOrder M := by
  first | exact @GlobalTheory.PicReducedTors.pic_isOfFinOrder | exact GlobalTheory.PicReducedTors.pic_isOfFinOrder | (intros; apply GlobalTheory.PicReducedTors.pic_isOfFinOrder <;> assumption)
end _root_.GlobalTheory.T
