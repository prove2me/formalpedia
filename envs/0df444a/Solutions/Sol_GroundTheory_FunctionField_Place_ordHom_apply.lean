-- Prove2me | solution 1 for GroundTheory.FunctionField.Place.ordHom_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:01:07.837955+00:00
-- url     : https://prove2.me/submissions/540b5b09-ceb8-43b1-9664-73c4399e92a6

import Mathlib
import Definitions.Def_GroundTheory_FunctionField_PlaceDefs

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
theorem _root_.solution (x : Kˣ) : v.ordHom x = Multiplicative.ofAdd (v.ord x) :=
  rfl
end GroundTheory.FunctionField.Place
