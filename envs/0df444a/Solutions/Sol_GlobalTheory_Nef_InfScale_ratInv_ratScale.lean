-- Prove2me | solution 1 for GlobalTheory.Nef.InfScale.ratInv_ratScale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:21:47.693791+00:00
-- url     : https://prove2.me/submissions/1dae42e0-6992-466f-ad62-7e1b2d9d77d0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsScalingCompatibleExpansionAtInfinity
import Theorems.Thm_GlobalTheory_Nef_InfScale_ext_rat
import Theorems.Thm_GlobalTheory_Nef_InfScale_ratScale_C
import Theorems.Thm_GlobalTheory_Nef_InfScale_ratScale_X
import Theorems.Thm_GlobalTheory_Nef_InfScale_ratInv_C
import Theorems.Thm_GlobalTheory_Nef_InfScale_ratInv_X
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
open GlobalTheory.Nef
open GlobalTheory GlobalTheory.Nef GlobalTheory.Nef.InfScale
variable {F : Type} [Field F]
namespace GlobalTheory.Nef.InfScale
theorem _root_.solution (c : F) (hc : c ≠ 0) :
    ratInv.comp (ratScale c hc) = (ratScale c⁻¹ (inv_ne_zero hc)).comp ratInv := by
  apply ext_rat
  · intro a; simp only [RingHom.comp_apply, ratScale_C, ratInv_C]
  · simp only [RingHom.comp_apply, ratScale_X, ratInv_X, map_mul, ratInv_C, map_inv₀, mul_inv,
      inv_inv]
end GlobalTheory.Nef.InfScale
