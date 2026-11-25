-- Prove2me | solution 1 for GroundTheory.FunctionField.Place.LiesOver.isScalarTower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:05:15.136566+00:00
-- url     : https://prove2.me/submissions/fe3a3e92-cbf9-4dd2-812b-83729d9db206

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
namespace GroundTheory.FunctionField.Place
namespace LiesOver
theorem _root_.solution {w : Place k K'} {v : Place k K} (h : w.LiesOver v) :
    let := h.algebra
    IsScalarTower k v.ring w.ring := by
  let := h.algebra
  exact IsScalarTower.of_algebraMap_eq fun c =>
    Subtype.ext (IsScalarTower.algebraMap_apply k K K' c)
end LiesOver
end GroundTheory.FunctionField.Place
