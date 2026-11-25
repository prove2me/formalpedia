-- Prove2me | solution 1 for GlobalTheory.Nef.FundId.toRing_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:11:32.960647+00:00
-- url     : https://prove2.me/submissions/121b3209-bcd6-4a77-a807-69a92fdac8bb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_GroundTheory_FunctionField_PlaceSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FunctionFieldPlaceSumOrderEqFinrank
import Theorems.Thm_GlobalTheory_Nef_FundId_valuation_toRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef
open GlobalTheory GlobalTheory.Nef GlobalTheory.Nef.FundId
variable {k F : Type} [Field k] [Field F] [Algebra k F]
namespace GlobalTheory.Nef.FundId
theorem _root_.solution [GroundTheory.FunctionField.IsFunctionField k F] :
    Function.Injective (toRing : Place k F → _) := fun v w h =>
  Subtype.ext (by rw [← valuation_toRing, ← valuation_toRing, h])
end GlobalTheory.Nef.FundId
