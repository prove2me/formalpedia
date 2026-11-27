-- Prove2me | solution 1 for GroundTheory.ProfCoh.IsProPGroup.of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:50:48.618834+00:00
-- url     : https://prove2.me/submissions/91a6d6ad-99ba-4751-adba-2a9240c7d75a

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_OpenNormal
import Definitions.Def_GroundTheory_ProfiniteCohomology_OfNatRelIndexSupAntitone
import Definitions.Def_GroundTheory_ProfiniteCohomology_IsProPGroupSubgroupIffIsPGroupMap
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
namespace IsProPGroup
theorem _root_.solution {p : ℕ} {H K : Subgroup G} (hH : IsProPGroup p H) (hKH : K ≤ H) :
    IsProPGroup p K := by
  rw [isProPGroup_subgroup_iff] at hH ⊢
  exact fun U k hk => hH U k (hKH hk)
end IsProPGroup
end GroundTheory.ProfCoh
