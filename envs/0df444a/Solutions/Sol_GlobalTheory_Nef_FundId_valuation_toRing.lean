-- Prove2me | solution 1 for GlobalTheory.Nef.FundId.valuation_toRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:01:54.438828+00:00
-- url     : https://prove2.me/submissions/75dfa1cb-ac74-4041-afb9-28b309c1c9d7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_GroundTheory_FunctionField_PlaceSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FunctionFieldPlaceSumOrderEqFinrank
import Theorems.Thm_GroundTheory_FunctionField_Place_valuation_le_one_iff
import Theorems.Thm_GroundTheory_FunctionField_Place_valuation_surjective
import Theorems.Thm_GroundTheory_FunctionField_valuation_eq_of_isEquiv


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
theorem _root_.solution [GroundTheory.FunctionField.IsFunctionField k F] (v : Place k F) :
    (toRing v).valuation = v.1 := by
  refine GroundTheory.FunctionField.valuation_eq_of_isEquiv ?_ (toRing v).valuation_surjective v.2.1
  refine Valuation.isEquiv_iff_val_le_one.2 fun {x} => ?_
  rw [GroundTheory.FunctionField.Place.valuation_le_one_iff]
  rfl
end GlobalTheory.Nef.FundId
