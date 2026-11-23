-- Prove2me | solution 1 for GroundTheory.FunctionField.Place.uniformizer_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:43:43.103116+00:00
-- url     : https://prove2.me/submissions/d7ba3dec-7383-4c13-bf46-a51c43913faf

import Mathlib
import Definitions.Def_GroundTheory_FunctionField_PlaceBasic
import Definitions.Def_GroundTheory_FunctionField_PlaceAbove
import Theorems.Thm_GroundTheory_FunctionField_Place_ord_uniformizer

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
namespace GroundTheory.FunctionField.Place
theorem _root_.solution (v : Place k K) : v.uniformizer ≠ 0 := fun h => by
  have h1 := v.ord_uniformizer
  rw [h, ord_zero] at h1
  exact zero_ne_one h1
end GroundTheory.FunctionField.Place
