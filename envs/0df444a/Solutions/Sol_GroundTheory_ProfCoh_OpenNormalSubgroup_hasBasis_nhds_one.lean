-- Prove2me | solution 1 for GroundTheory.ProfCoh.OpenNormalSubgroup.hasBasis_nhds_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:12:42.541774+00:00
-- url     : https://prove2.me/submissions/2771ab91-6011-46af-b6f8-fe55b76da081

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_OpenNormal
import Theorems.Thm_GroundTheory_ProfCoh_OpenNormalSubgroup_mem_nhds_one

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
open Filter Topology
variable {G : Type*} [Group G] [TopologicalSpace G]
open GroundTheory.ProfCoh.OpenNormalSubgroup
variable [IsTopologicalGroup G]
variable [CompactSpace G] [TotallyDisconnectedSpace G]
namespace GroundTheory.ProfCoh.OpenNormalSubgroup
theorem _root_.solution :
    (𝓝 (1 : G)).HasBasis (fun _ : OpenNormalSubgroup G => True) (fun U => (U : Set G)) := by
  refine ⟨fun s => ⟨fun hs => ?_, fun ⟨U, _, hU⟩ => mem_of_superset U.mem_nhds_one hU⟩⟩
  obtain ⟨t, hts, ht, h1⟩ := mem_nhds_iff.mp hs
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one ht h1
  exact ⟨U, trivial, hU.trans hts⟩
end GroundTheory.ProfCoh.OpenNormalSubgroup
