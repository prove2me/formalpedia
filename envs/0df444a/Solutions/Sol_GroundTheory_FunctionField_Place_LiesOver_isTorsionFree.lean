-- Prove2me | solution 1 for GroundTheory.FunctionField.Place.LiesOver.isTorsionFree
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:39:41.074548+00:00
-- url     : https://prove2.me/submissions/2df84c6a-9f8b-435c-b5e5-79697803246c

import Mathlib
import Definitions.Def_GroundTheory_FunctionField_PlaceBasic
import Definitions.Def_GroundTheory_FunctionField_PlaceAbove

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.FunctionField
open GroundTheory.FunctionField.Place
variable {k K K' : Type*} [Field k] [Field K] [Field K'] [Algebra k K] [Algebra k K']
  [Algebra K K'] [IsScalarTower k K K']
variable [IsFunctionField k K]
variable [IsFunctionField k K']
omit [IsFunctionField k K] [IsFunctionField k K'] [IsScalarTower k K K']
namespace GroundTheory.FunctionField.Place
namespace LiesOver
theorem _root_.solution {w : Place k K'} {v : Place k K} (h : w.LiesOver v) :
    letI := h.algebra
    Module.IsTorsionFree v.ring w.ring := by
  let := h.algebra
  exact Module.isTorsionFree_iff_algebraMap_injective.2 fun a b hab =>
    Subtype.ext ((algebraMap K K').injective (congrArg Subtype.val hab))
end LiesOver
end GroundTheory.FunctionField.Place
