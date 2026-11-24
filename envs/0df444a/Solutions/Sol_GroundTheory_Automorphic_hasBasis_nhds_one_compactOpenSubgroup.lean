-- Prove2me | solution 1 for GroundTheory.Automorphic.hasBasis_nhds_one_compactOpenSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:34:17.019102+00:00
-- url     : https://prove2.me/submissions/80f5b6c4-3d14-41e1-b34c-24c42193e8dc

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Theorems.Thm_GroundTheory_Automorphic_exists_openSubgroup_isCompact_subset

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Set Filter Topology MeasureTheory
open scoped Pointwise
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
namespace GroundTheory.Automorphic
theorem _root_.solution :
    (𝓝 (1 : G)).HasBasis (fun K : OpenSubgroup G => IsCompact (K : Set G))
      (fun K => (K : Set G)) :=
  ⟨fun _ => ⟨fun hU => exists_openSubgroup_isCompact_subset hU,
    fun ⟨K, _, hKU⟩ => mem_of_superset K.mem_nhds_one hKU⟩⟩
end GroundTheory.Automorphic
