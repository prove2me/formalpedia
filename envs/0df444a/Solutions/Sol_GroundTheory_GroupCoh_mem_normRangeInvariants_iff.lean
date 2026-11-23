-- Prove2me | solution 1 for GroundTheory.GroupCoh.mem_normRangeInvariants_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:07:24.655847+00:00
-- url     : https://prove2.me/submissions/85b2c37e-6211-4645-a76a-f7637a63ded2

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
theorem _root_.solution (M : Rep.{u} R G) (x : M.ρ.invariants) :
    x ∈ normRangeInvariants M ↔ ∃ m, M.ρ.norm m = x := Iff.rfl
end GroundTheory.GroupCoh
