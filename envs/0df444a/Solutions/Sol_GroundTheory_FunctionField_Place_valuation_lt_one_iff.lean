-- Prove2me | solution 1 for GroundTheory.FunctionField.Place.valuation_lt_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:16:05.943241+00:00
-- url     : https://prove2.me/submissions/85a0ba64-e697-4da3-a2aa-79be20dd7139

import Mathlib
import Definitions.Def_GroundTheory_FunctionField_PlaceDefs
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
open IntermediateField
open scoped WithZero
open Polynomial
variable (k K : Type*) [Field k] [Field K] [Algebra k K]
open GroundTheory.FunctionField.Place
variable {k K} (v : Place k K)
variable [IsFunctionField k K]
namespace GroundTheory.FunctionField.Place
theorem _root_.solution (x : K) : v.valuation x < 1 ↔ v.ring.valuation x < 1 :=
  v.valuation_isEquiv.lt_one_iff_lt_one
end GroundTheory.FunctionField.Place
