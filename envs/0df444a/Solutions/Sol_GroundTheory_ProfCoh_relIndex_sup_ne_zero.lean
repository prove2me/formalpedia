-- Prove2me | solution 1 for GroundTheory.ProfCoh.relIndex_sup_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:48:32.355798+00:00
-- url     : https://prove2.me/submissions/e9898be8-b3fa-41fe-9875-be7d2d43fc40

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_OpenNormal
import Definitions.Def_GroundTheory_ProfiniteCohomology_Supernatural
import Definitions.Def_GroundTheory_ProfiniteCohomology_OfNatRelIndexSupAntitone

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open Topology
variable {G : Type*} [Group G]
variable [TopologicalSpace G]
variable [IsTopologicalGroup G] [CompactSpace G]
namespace GroundTheory.ProfCoh
theorem _root_.solution (K H : Subgroup G) (U : OpenNormalSubgroup G) :
    (K ⊔ (U : Subgroup G)).relIndex H ≠ 0 :=
  fun h => Subgroup.FiniteIndex.index_ne_zero (H := (U : Subgroup G))
    (Nat.eq_zero_of_zero_dvd (h ▸ (Subgroup.relIndex_dvd_of_le_left H le_sup_right).trans
      (Subgroup.relIndex_dvd_index_of_normal (U : Subgroup G) H)))
end GroundTheory.ProfCoh
