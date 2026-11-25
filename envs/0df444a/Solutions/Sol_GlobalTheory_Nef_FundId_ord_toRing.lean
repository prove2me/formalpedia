-- Prove2me | solution 1 for GlobalTheory.Nef.FundId.ord_toRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:19:10.875895+00:00
-- url     : https://prove2.me/submissions/4e5dfdf5-64dc-4b03-9d47-9f1b088aa20c

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
theorem _root_.solution [GroundTheory.FunctionField.IsFunctionField k F] (v : Place k F) (x : F) :
    (toRing v).ord x = ord v x := by
  unfold ord
  rw [← valuation_toRing]
  rfl
end GlobalTheory.Nef.FundId
