-- Prove2me | solution 1 for GroundTheory.FunctionField.Place.ord_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:43:25.341382+00:00
-- url     : https://prove2.me/submissions/21a6986c-a333-4fc7-995a-880019bc4256

import Mathlib
import Definitions.Def_GroundTheory_FunctionField_PlaceDefs
import Theorems.Thm_P2M_GroundTheory_FunctionField_Place_valuation_algebraMap__1215bcdcaa8c

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
theorem _root_.solution {c : k} (hc : c ≠ 0) : v.ord (algebraMap k K c) = 0 := by
  rw [ord, v.valuation_algebraMap' hc, WithZero.log_one, neg_zero]
end GroundTheory.FunctionField.Place
