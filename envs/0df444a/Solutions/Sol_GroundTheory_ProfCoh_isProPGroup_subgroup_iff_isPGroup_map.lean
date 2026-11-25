-- Prove2me | solution 1 for GroundTheory.ProfCoh.isProPGroup_subgroup_iff_isPGroup_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:39:54.419483+00:00
-- url     : https://prove2.me/submissions/9988c42b-bd9e-4a4c-aaa7-30f2adfd9cae

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_OpenNormal
import Definitions.Def_GroundTheory_ProfiniteCohomology_OfNatRelIndexSupAntitone
import Definitions.Def_GroundTheory_ProfiniteCohomology_IsProPGroupSubgroupIffIsPGroupMap
import Theorems.Thm_GroundTheory_ProfCoh_isPGroup_map_mk_iff
import Theorems.Thm_GroundTheory_ProfCoh_isProPGroup_subgroup_iff

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
variable {G : Type*} [Group G] [TopologicalSpace G]
variable [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
namespace GroundTheory.ProfCoh
theorem _root_.solution {p : ℕ} {H : Subgroup G} :
    IsProPGroup p H ↔
      ∀ U : OpenNormalSubgroup G, IsPGroup p (H.map (QuotientGroup.mk' (U : Subgroup G))) := by
  rw [isProPGroup_subgroup_iff]
  exact forall_congr' fun U => (isPGroup_map_mk_iff H (U : Subgroup G)).symm
end GroundTheory.ProfCoh
