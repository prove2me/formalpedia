-- Prove2me | solution 1 for GroundTheory.Global.exists_openSubgroup_subset_of_profinite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:08:47.992934+00:00
-- url     : https://prove2.me/submissions/a3a95007-ff49-47f6-9d12-f7384a137e13

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_NoSmallSubgroups

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open Topology Filter
variable {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H]
namespace GroundTheory.Global
theorem _root_.solution [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G] {W : Set G} (hW : W ∈ 𝓝 (1 : G)) :
    ∃ V : OpenSubgroup G, (V : Set G) ⊆ W := by
  obtain ⟨C, ⟨hC1, hCc⟩, hCW⟩ := (nhds_basis_clopen (1 : G)).mem_iff.1 hW
  obtain ⟨V, hV⟩ := IsTopologicalGroup.exist_openSubgroup_sub_clopen_nhds_of_one hCc hC1
  exact ⟨V, hV.trans hCW⟩
end GroundTheory.Global
