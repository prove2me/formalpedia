-- Prove2me | solution 1 for GroundTheory.Automorphic.exists_compactOpenSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:49:03.592812+00:00
-- url     : https://prove2.me/submissions/e64d22f3-01ba-4fb3-80d7-8fe6bb83d47f

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
theorem _root_.solution : ∃ K : OpenSubgroup G, IsCompact (K : Set G) := by
  obtain ⟨K, hK, -⟩ := exists_openSubgroup_isCompact_subset (univ_mem : univ ∈ 𝓝 (1 : G))
  exact ⟨K, hK⟩
end GroundTheory.Automorphic
