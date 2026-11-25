-- Prove2me | solution 1 for GlobalTheory.Nef.ord_zpow_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:09:39.553023+00:00
-- url     : https://prove2.me/submissions/9e81b80a-dbd0-4c17-b424-4802fbdd152f

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TwistAtOfNe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AdmissibleDegreeTwistFamilyAtPlaceByScalar
import Theorems.Thm_GroundTheory_FunctionField_Place_ordHom_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.FunctionField.Place.ordHom_apply



set_option autoImplicit false
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef Polynomial
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Nef
namespace GlobalTheory.Nef
theorem _root_.solution {k F : Type} [Field k] [Field F] [Algebra k F] (v : Place k F) {x : F} (hx : x ≠ 0)
    (m : ℤ) : ord v (x ^ m) = m * ord v x := by
  have h0 : v.1 x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  simp only [ord, map_zpow₀]
  rw [← WithZero.exp_log h0, ← WithZero.exp_zsmul, WithZero.log_exp, WithZero.log_exp, smul_eq_mul]
  ring
end GlobalTheory.Nef
