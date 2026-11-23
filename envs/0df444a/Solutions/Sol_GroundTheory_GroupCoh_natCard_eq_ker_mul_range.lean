-- Prove2me | solution 1 for GroundTheory.GroupCoh.natCard_eq_ker_mul_range
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:11:46.949313+00:00
-- url     : https://prove2.me/submissions/66534312-9607-47f5-89d5-c269bfabcba5

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.GroupCoh
namespace GroundTheory.GroupCoh
theorem _root_.solution {X Y : Type*} [AddGroup X] [AddGroup Y] (φ : X →+ Y) :
    Nat.card X = Nat.card φ.ker * Nat.card φ.range := by
  rw [← AddSubgroup.index_ker φ, AddSubgroup.card_mul_index]
end GroundTheory.GroupCoh
