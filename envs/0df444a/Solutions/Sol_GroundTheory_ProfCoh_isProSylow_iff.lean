-- Prove2me | solution 1 for GroundTheory.ProfCoh.isProSylow_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:51:01.389553+00:00
-- url     : https://prove2.me/submissions/faba405c-0a49-41c8-90cf-dcd5fdde1561

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_OpenNormal
import Definitions.Def_GroundTheory_ProfiniteCohomology_Supernatural
import Definitions.Def_GroundTheory_ProfiniteCohomology_OfNatRelIndexSupAntitone
import Definitions.Def_GroundTheory_ProfiniteCohomology_IsProPGroupSubgroupIffIsPGroupMap
import Definitions.Def_GroundTheory_ProfiniteCohomology_NotDvdSuperIndexIffMap
import Theorems.Thm_GroundTheory_ProfCoh_isProPGroup_subgroup_iff_isPGroup_map


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
open Pointwise CategoryTheory
variable {G : Type*} [Group G]
variable [TopologicalSpace G]
variable [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
variable {p : ℕ} [hp : Fact p.Prime]
namespace GroundTheory.ProfCoh
theorem _root_.solution {P : Subgroup G} (hP : IsClosed (P : Set G)) :
    IsProSylow p P ↔ ∀ U : OpenNormalSubgroup G,
      IsPGroup p (P.map (QuotientGroup.mk' (U : Subgroup G))) ∧
        ¬ p ∣ (P.map (QuotientGroup.mk' (U : Subgroup G))).index := by
  rw [IsProSylow, isProPGroup_subgroup_iff_isPGroup_map, not_dvd_superIndex_iff_map, ← forall_and]
  exact ⟨fun h => h.2, fun h => ⟨hP, h⟩⟩
end GroundTheory.ProfCoh
