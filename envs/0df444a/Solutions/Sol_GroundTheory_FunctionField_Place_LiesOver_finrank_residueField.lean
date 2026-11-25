-- Prove2me | solution 1 for GroundTheory.FunctionField.Place.LiesOver.finrank_residueField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:17:27.010502+00:00
-- url     : https://prove2.me/submissions/9819d894-2f49-43dc-a4fb-d3a77578b2b1

import Mathlib
import Definitions.Def_GroundTheory_FunctionField_PlaceBasic
import Definitions.Def_GroundTheory_FunctionField_PlaceAbove
import Theorems.Thm_GroundTheory_FunctionField_Place_LiesOver_deg_mul_finrank
import Theorems.Thm_GroundTheory_FunctionField_Place_deg_pos


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
omit [IsFunctionField k K']
namespace GroundTheory.FunctionField.Place
namespace LiesOver
theorem _root_.solution {w : Place k K'} {v : Place k K} (h : w.LiesOver v) :
    letI := h.algebra
    letI := h.isLocalHom
    Module.finrank v.ResidueField w.ResidueField = w.inertiaDeg v := by
  let := h.algebra
  have := h.isLocalHom
  rw [inertiaDeg, ← h.deg_mul_finrank, Nat.mul_div_cancel_left _ v.deg_pos]
end LiesOver
end GroundTheory.FunctionField.Place
