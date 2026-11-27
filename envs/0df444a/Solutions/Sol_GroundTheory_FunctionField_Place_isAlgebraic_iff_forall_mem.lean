-- Prove2me | solution 1 for GroundTheory.FunctionField.Place.isAlgebraic_iff_forall_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:45:16.05402+00:00
-- url     : https://prove2.me/submissions/f97668c8-84c6-424a-8921-dcbe1a268084

import Mathlib
import Definitions.Def_GroundTheory_FunctionField_PlaceDefs
import Definitions.Def_GroundTheory_FunctionField_PlaceBasic
import Theorems.Thm_GroundTheory_FunctionField_Place_exists_not_mem_of_transcendental

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.FunctionField
open Polynomial
open GroundTheory.FunctionField.Place
variable {k K : Type*} [Field k] [Field K] [Algebra k K]
namespace GroundTheory.FunctionField.Place
theorem _root_.solution {x : K} : IsAlgebraic k x ↔ ∀ v : Place k K, x ∈ v.ring := by
  refine ⟨fun hx v => v.mem_ring_of_isAlgebraic hx, fun h => ?_⟩
  by_contra hx
  obtain ⟨v, hv⟩ := exists_not_mem_of_transcendental hx
  exact hv (h v)
end GroundTheory.FunctionField.Place
