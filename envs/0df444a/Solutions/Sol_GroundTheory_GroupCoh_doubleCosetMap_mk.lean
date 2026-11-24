-- Prove2me | solution 1 for GroundTheory.GroupCoh.doubleCosetMap_mk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:22:12.560383+00:00
-- url     : https://prove2.me/submissions/776b847e-a455-4b8e-9673-da625c6cb6bb

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_DoubleCosetSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open Pointwise
open GroundTheory GroundTheory.GroupCoh
variable {G : Type*} [Group G] (T S : Subgroup G)
namespace GroundTheory.GroupCoh
theorem _root_.solution (g : G) (t : T) :
    doubleCosetMap T S g (t : T ⧸ (T ⊓ MulAut.conj g • S).subgroupOf T) = ((t * g : G) : G ⧸ S) :=
  rfl
end GroundTheory.GroupCoh
