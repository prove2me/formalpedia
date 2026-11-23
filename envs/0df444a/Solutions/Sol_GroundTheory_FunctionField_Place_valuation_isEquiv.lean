-- Prove2me | solution 1 for GroundTheory.FunctionField.Place.valuation_isEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:01:40.46693+00:00
-- url     : https://prove2.me/submissions/071b246a-fdff-4f9c-ad37-dd8190070ef0

import Mathlib
import Definitions.Def_GroundTheory_FunctionField_PlaceDefs
import Theorems.Thm_GroundTheory_FunctionField_Place_valuation_le_one_iff

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
theorem _root_.solution : v.valuation.IsEquiv v.ring.valuation :=
  Valuation.isEquiv_iff_val_le_one.2 fun {x} =>
    (v.valuation_le_one_iff x).trans (v.ring.valuation_le_one_iff x).symm
end GroundTheory.FunctionField.Place
