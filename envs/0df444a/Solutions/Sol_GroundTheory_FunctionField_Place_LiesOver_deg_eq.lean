-- Prove2me | solution 1 for GroundTheory.FunctionField.Place.LiesOver.deg_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:45:08.931126+00:00
-- url     : https://prove2.me/submissions/0b673cc7-6240-4da8-9ea2-e085ffd358d3

import Mathlib
import Definitions.Def_GroundTheory_FunctionField_PlaceBasic
import Definitions.Def_GroundTheory_FunctionField_PlaceAbove
import Theorems.Thm_GroundTheory_FunctionField_Place_LiesOver_deg_mul_finrank
import Theorems.Thm_GroundTheory_FunctionField_Place_LiesOver_finrank_residueField

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
namespace GroundTheory.FunctionField.Place
namespace LiesOver
theorem _root_.solution {w : Place k K'} {v : Place k K} (h : w.LiesOver v) :
    w.deg = w.inertiaDeg v * v.deg := by
  let := h.algebra
  have := h.isLocalHom
  rw [← h.finrank_residueField, ← h.deg_mul_finrank, mul_comm]
end LiesOver
end GroundTheory.FunctionField.Place
