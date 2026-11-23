-- Prove2me | solution 1 for GroundTheory.FunctionField.Place.ord_uniformizer
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:28:53.594259+00:00
-- url     : https://prove2.me/submissions/bd829120-2be4-407a-aad6-60962e41665c

import Mathlib
import Definitions.Def_GroundTheory_FunctionField_PlaceBasic
import Definitions.Def_GroundTheory_FunctionField_PlaceAbove
import Theorems.Thm_GroundTheory_FunctionField_Place_exists_ord_eq_one


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
theorem _root_.solution (v : Place k K) : v.ord v.uniformizer = 1 :=
  Classical.choose_spec v.exists_ord_eq_one
end GroundTheory.FunctionField.Place
