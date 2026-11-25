-- Prove2me | solution 1 for GroundTheory.GroupCoh.nsmul_eq_zero_coind
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:37:36.004486+00:00
-- url     : https://prove2.me/submissions/00fd100a-6b3b-4e1d-b284-1831bcec4452

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
theorem _root_.solution (M : Rep.{u} k G) {n : ℕ} (hM : ∀ x : M, n • x = 0)
    (x : coind (⊥ : Subgroup G).subtype (res (⊥ : Subgroup G).subtype M)) : n • x = 0 :=
  Subtype.ext (funext fun g => hM (x.1 g))
end GroundTheory.GroupCoh
