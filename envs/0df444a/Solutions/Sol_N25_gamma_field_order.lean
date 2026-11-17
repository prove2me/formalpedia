-- Prove2me | solution 1 for N25.gamma_field_order
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:44:25.842972+00:00
-- url     : https://prove2.me/submissions/9b2299a6-c286-4c25-a6b5-a72e335d7174

import Mathlib
import Definitions.Def_N25
import Theorems.Thm_N25_diamondField_order_five
import Theorems.Thm_ModularCurve_diamondAutHBar_mul_and_diamondAutHBar_one

set_option autoImplicit false

namespace N25

/-- The label-thirteen field diamond has exact order five. -/
theorem _root_.solution :
    orderOf (ModularCurve.diamondAutHBar 25 H25
      (ZMod.unitOfCoprime 13 (by decide))) = 5 := by
  obtain ⟨hmul, hone⟩ := ModularCurve.diamondAutHBar_mul_and_diamondAutHBar_one 25 H25
  let D : (ZMod 25)ˣ →*
      (ModularCurve.xHFunctionFieldBar 25 H25 ≃ₐ[AlgebraicClosure ℚ]
        ModularCurve.xHFunctionFieldBar 25 H25) :=
    { toFun := ModularCurve.diamondAutHBar 25 H25
      map_one' := hone
      map_mul' := hmul }
  have hlabels : ZMod.unitOfCoprime 13 (by decide : Nat.Coprime 13 25) =
      (ZMod.unitOfCoprime 2 (by decide : Nat.Coprime 2 25))⁻¹ := by
    apply eq_inv_iff_mul_eq_one.mpr
    decide
  change orderOf (D (ZMod.unitOfCoprime 13 (by decide))) = 5
  rw [hlabels, map_inv, orderOf_inv]
  exact diamondField_order_five

end N25
