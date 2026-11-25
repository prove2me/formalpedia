-- Prove2me | solution 1 for GroundTheory.GroupCoh.nsmul_eq_zero_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:48:59.427223+00:00
-- url     : https://prove2.me/submissions/2eba7327-9f96-4be3-897f-01edce3508ad

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
    (hf : Function.Surjective f.hom) {n : ℕ} (hA : ∀ x : A, n • x = 0) (y : B) : n • y = 0 := by
  obtain ⟨x, rfl⟩ := hf y
  change n • f.hom.toLinearMap x = 0
  rw [← map_nsmul, hA, map_zero]
end GroundTheory.GroupCoh
