-- Prove2me | solution 1 for GroundTheory.ProfCoh.isProPGroup_subgroup_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:32:42.139638+00:00
-- url     : https://prove2.me/submissions/9ac23c6f-c22c-4d0e-a3a4-a4ed80b0dcb5

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_OpenNormal
import Definitions.Def_GroundTheory_ProfiniteCohomology_OfNatRelIndexSupAntitone
import Definitions.Def_GroundTheory_ProfiniteCohomology_IsProPGroupSubgroupIffIsPGroupMap
import Theorems.Thm_GroundTheory_ProfCoh_isProPGroup_iff
import Theorems.Thm_GroundTheory_ProfCoh_exists_subgroupOf_le

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
    IsProPGroup p H ↔ ∀ U : OpenNormalSubgroup G, ∀ h ∈ H, ∃ k : ℕ, h ^ p ^ k ∈ U := by
  rw [isProPGroup_iff]
  constructor
  · intro hH U h hh
    let U' : OpenNormalSubgroup H :=
      { toSubgroup := (U : Subgroup G).subgroupOf H
        isOpen' := Subgroup.subgroupOf_isOpen H (U : Subgroup G) U.toOpenSubgroup.isOpen
        isNormal' := inferInstance }
    obtain ⟨k, hk⟩ := hH U' ⟨h, hh⟩
    exact ⟨k, hk⟩
  · intro hH V g
    obtain ⟨U, hU⟩ := exists_subgroupOf_le V
    obtain ⟨k, hk⟩ := hH U g g.2
    exact ⟨k, hU (show (g ^ p ^ k : H) ∈ (U : Subgroup G).subgroupOf H from hk)⟩
end GroundTheory.ProfCoh
