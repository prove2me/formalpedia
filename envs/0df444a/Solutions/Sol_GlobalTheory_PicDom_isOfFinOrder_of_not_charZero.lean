-- Prove2me | solution 1 for GlobalTheory.PicDom.isOfFinOrder_of_not_charZero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:27:08.039042+00:00
-- url     : https://prove2.me/submissions/0ba6c879-4ff5-4433-acfe-e63208d0daac

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOfFinOrderOfIsOfFinOrderMapRingHomStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PicIsOfFinOrderOfFiniteInt

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
namespace GlobalTheory.PicDom
theorem _root_.solution (B : Type) [CommRing B] [IsDomain B] [Module.Finite ℤ B]
    (hc : ¬ CharZero B) (M : CommRing.Pic B) : IsOfFinOrder M := by
  have hp : ringChar B ≠ 0 := by
    intro h
    apply hc
    have : CharP B 0 := h ▸ ringChar.charP B
    exact CharP.charP_to_charZero B
  have hfin : Finite B := Module.finite_of_fg_torsion B fun x =>
    ⟨⟨(ringChar B : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hp)⟩, by
      change ((ringChar B : ℤ)) • x = 0
      rw [zsmul_eq_mul, Int.cast_natCast, ringChar.Nat.cast_ringChar, zero_mul]⟩
  exact isOfFinOrder_of_finite M
end GlobalTheory.PicDom
