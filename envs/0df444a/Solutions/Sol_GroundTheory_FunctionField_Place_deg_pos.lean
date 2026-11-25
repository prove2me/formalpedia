-- Prove2me | solution 1 for GroundTheory.FunctionField.Place.deg_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:05:16.941082+00:00
-- url     : https://prove2.me/submissions/cb9b2d0e-435a-499f-a9b1-4535026e1f17

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
namespace GroundTheory.FunctionField.Place
theorem _root_.solution [IsFunctionField k K] : 0 < v.deg := Module.finrank_pos
end GroundTheory.FunctionField.Place
