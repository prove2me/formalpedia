-- Prove2me | solution 1 for GroundTheory.ProfCoh.OpenNormalSubgroup.hasBasis_nhds_one_pi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:50:52.414798+00:00
-- url     : https://prove2.me/submissions/12325e4b-071c-4301-9db3-d3e7dd62d9f1

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_OpenNormal
import Theorems.Thm_GroundTheory_ProfCoh_OpenNormalSubgroup_hasBasis_nhds_one

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
theorem _root_.solution (ι : Type*) [Finite ι] :
    (𝓝 (1 : ι → G)).HasBasis (fun _ : OpenNormalSubgroup G => True)
      (fun U => Set.univ.pi fun _ => (U : Set G)) := by
  simp only [nhds_pi, Pi.one_apply]
  refine (hasBasis_nhds_one.pi_self (ι := ι)).to_hasBasis ?_ ?_
  · rintro ⟨I, U⟩ -
    exact ⟨U, trivial, fun x hx i _ => hx i (Set.mem_univ i)⟩
  · intro U _
    exact ⟨⟨Set.univ, U⟩, ⟨Set.finite_univ, trivial⟩, subset_rfl⟩
end GroundTheory.ProfCoh.OpenNormalSubgroup
