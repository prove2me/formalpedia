-- Prove2me | solution 1 for GroundTheory.GroupCoh.nsmul_eq_zero_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:48:44.077929+00:00
-- url     : https://prove2.me/submissions/f0ed29e1-dc5a-4010-831c-a4fd69e1c3b6

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
theorem _root_.solution {A B : Rep.{u} k G} (f : A ⟶ B)
    (hf : Function.Injective f.hom) {n : ℕ} (hB : ∀ y : B, n • y = 0) (x : A) : n • x = 0 := by
  apply hf
  change f.hom.toLinearMap (n • x) = f.hom.toLinearMap 0
  rw [map_nsmul, map_zero]
  exact hB _
end GroundTheory.GroupCoh
