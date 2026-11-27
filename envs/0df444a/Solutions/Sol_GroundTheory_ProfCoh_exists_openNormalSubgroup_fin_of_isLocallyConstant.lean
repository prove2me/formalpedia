-- Prove2me | solution 1 for GroundTheory.ProfCoh.exists_openNormalSubgroup_fin_of_isLocallyConstant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:49:12.010535+00:00
-- url     : https://prove2.me/submissions/db832475-340b-4fe6-b38d-93964a7341df

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_OpenNormal
import Definitions.Def_GroundTheory_ProfiniteCohomology_Factor
import Theorems.Thm_GroundTheory_ProfCoh_exists_openNormalSubgroup_pi_of_isLocallyConstant

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
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]
namespace GroundTheory.ProfCoh
theorem _root_.solution {n : ℕ} {X : Type*}
    {f : (Fin n → G) → X} (hf : IsLocallyConstant f) :
    ∃ U : OpenNormalSubgroup G, ∀ x y : Fin n → G, (∀ i, (x i)⁻¹ * y i ∈ U) → f x = f y :=
  exists_openNormalSubgroup_pi_of_isLocallyConstant hf
end GroundTheory.ProfCoh
