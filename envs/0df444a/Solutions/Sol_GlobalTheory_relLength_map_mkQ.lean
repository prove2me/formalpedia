-- Prove2me | solution 1 for GlobalTheory.relLength_map_mkQ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:36:57.913651+00:00
-- url     : https://prove2.me/submissions/9cacb326-eb74-4c6f-8a4d-ed3554521bee

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
import Theorems.Thm_GlobalTheory_relLength_map_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]
namespace GlobalTheory
theorem _root_.solution {N B : Submodule R V} (h : N ≤ B) (A : Submodule R V) :
    relLength (A.map N.mkQ) (B.map N.mkQ) = relLength A B := by
  rw [relLength_map_map, Submodule.ker_mkQ, sup_eq_left.mpr h]
end GlobalTheory
