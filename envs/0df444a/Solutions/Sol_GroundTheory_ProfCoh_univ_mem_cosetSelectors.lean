-- Prove2me | solution 1 for GroundTheory.ProfCoh.univ_mem_cosetSelectors
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:25:42.071197+00:00
-- url     : https://prove2.me/submissions/4fd45cf1-c044-46f4-9d76-14d92d34a414

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_OpenNormal
import Definitions.Def_GroundTheory_ProfiniteCohomology_InflationRestriction_Section

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
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
omit [IsTopologicalGroup G]
namespace GroundTheory.ProfCoh
theorem _root_.solution (N : Subgroup G) [N.Normal] (hN : IsClosed (N : Set G)) :
    Set.univ ∈ cosetSelectors N :=
  ⟨isClosed_univ, N, inferInstance, hN, le_rfl, fun _ _ _ _ => Set.mem_univ _,
    fun x => ⟨x, Set.mem_univ _, rfl⟩, fun _ _ _ _ h => QuotientGroup.eq.mp h⟩
end GroundTheory.ProfCoh
