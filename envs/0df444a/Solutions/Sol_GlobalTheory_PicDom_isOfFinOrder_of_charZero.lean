-- Prove2me | solution 1 for GlobalTheory.PicDom.isOfFinOrder_of_charZero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:56:57.204955+00:00
-- url     : https://prove2.me/submissions/3dfb4ee2-abfb-49d1-adbf-ab6928ee710d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOfFinOrderOfIsOfFinOrderMapRingHomStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PicIsOfFinOrderOfFiniteInt
import Theorems.Thm_GlobalTheory_PicDom_finiteDimensional_of_isFractionRing
import Theorems.Thm_GlobalTheory_PicDom_isOfFinOrder_of_numberField

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
open GlobalTheory GlobalTheory.PicDom
variable (B : Type) [CommRing B] [IsDomain B] [Module.Finite ℤ B] [CharZero B]
namespace GlobalTheory.PicDom
theorem _root_.solution (M : CommRing.Pic B) : IsOfFinOrder M := by
  haveI : CharZero (FractionRing B) := IsFractionRing.charZero_of_isFractionRing B
  haveI : FiniteDimensional ℚ (FractionRing B) := finiteDimensional_of_isFractionRing B (FractionRing B)
  haveI : NumberField (FractionRing B) := ⟨⟩
  exact isOfFinOrder_of_numberField B (FractionRing B) M
end GlobalTheory.PicDom
