-- Prove2me | solution 1 for GlobalTheory.pic_isOfFinOrder_of_finite_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:02:07.869847+00:00
-- url     : https://prove2.me/submissions/4cc7a8a0-9526-4a8b-b92e-8bfb9c489d96

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOfFinOrderOfIsOfFinOrderMapRingHomStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PicIsOfFinOrderOfFiniteInt
import Theorems.Thm_GlobalTheory_PicDom_isOfFinOrder_of_not_charZero
import Theorems.Thm_GlobalTheory_PicDom_isOfFinOrder_of_charZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open NumberField
namespace GlobalTheory
theorem _root_.solution : ∀ (B : Type) [CommRing B] [IsDomain B] [Module.Finite ℤ B]
    (M : CommRing.Pic B), IsOfFinOrder M := by
  intro B _ _ _ M
  by_cases hc : CharZero B
  · exact GlobalTheory.PicDom.isOfFinOrder_of_charZero B M
  · exact GlobalTheory.PicDom.isOfFinOrder_of_not_charZero B hc M
end GlobalTheory
