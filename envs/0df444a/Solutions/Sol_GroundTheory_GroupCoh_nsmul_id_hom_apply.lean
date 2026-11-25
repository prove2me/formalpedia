-- Prove2me | solution 1 for GroundTheory.GroupCoh.nsmul_id_hom_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:49:01.96426+00:00
-- url     : https://prove2.me/submissions/966ca400-5245-4db4-8e75-a70af5fa42ea

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_PGroupCohTrivial
import Definitions.Def_GroundTheory_TateCohomology_TateAddEquivAbelianizationTateClass
import Definitions.Def_GroundTheory_TateCohomology_PGroupCohTrivialInt

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
open CategoryTheory Limits Rep groupHomology
universe u
variable {k G : Type u} [CommRing k] [Group G]
namespace GroundTheory.GroupCoh
theorem _root_.solution (M : Rep.{u} k G) (n : ℕ) (x : M) : (n • 𝟙 M).hom x = n • x := by
  rw [Rep.nsmul_hom]; rfl
end GroundTheory.GroupCoh
