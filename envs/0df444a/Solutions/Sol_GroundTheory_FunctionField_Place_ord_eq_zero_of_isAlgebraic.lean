-- Prove2me | solution 1 for GroundTheory.FunctionField.Place.ord_eq_zero_of_isAlgebraic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:48:13.650725+00:00
-- url     : https://prove2.me/submissions/d560af52-62b6-40aa-8884-f5127ddaba20

import Mathlib
import Definitions.Def_GroundTheory_FunctionField_PlaceDefs
import Definitions.Def_GroundTheory_FunctionField_PlaceBasic
import Theorems.Thm_GroundTheory_FunctionField_Place_valuation_eq_one_of_isAlgebraic
import Theorems.Thm_GroundTheory_FunctionField_Place_valuation_isEquiv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.FunctionField
open Polynomial
open GroundTheory.FunctionField.Place
variable {k K : Type*} [Field k] [Field K] [Algebra k K]
namespace GroundTheory.FunctionField.Place
theorem _root_.solution [IsFunctionField k K] (v : Place k K) {x : K}
    (hx : IsAlgebraic k x) (hx0 : x ≠ 0) : v.ord x = 0 := by
  have h := v.valuation_eq_one_of_isAlgebraic hx hx0
  rw [← v.valuation_isEquiv.eq_one_iff_eq_one] at h
  rw [ord, h, WithZero.log_one, neg_zero]
end GroundTheory.FunctionField.Place
