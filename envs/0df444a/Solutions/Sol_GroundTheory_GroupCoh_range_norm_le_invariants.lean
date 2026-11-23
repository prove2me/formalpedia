-- Prove2me | solution 1 for GroundTheory.GroupCoh.range_norm_le_invariants
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:59:54.188088+00:00
-- url     : https://prove2.me/submissions/75a1451a-23bf-47b6-a844-b46f267181f1

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_ModuleHomologyData
import Definitions.Def_GroundTheory_TateCohomology_TateLow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.GroupCoh
open CategoryTheory Limits Representation groupCohomology groupHomology
universe u
variable {R G : Type u} [CommRing R] [Group G] [Fintype G]
namespace GroundTheory.GroupCoh
theorem _root_.solution (M : Rep.{u} R G) :
    LinearMap.range M.ρ.norm ≤ M.ρ.invariants := by
  rintro _ ⟨m, rfl⟩ g
  exact M.ρ.self_norm_apply g m
end GroundTheory.GroupCoh
