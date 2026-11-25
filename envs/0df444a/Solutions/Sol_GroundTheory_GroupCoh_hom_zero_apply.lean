-- Prove2me | solution 1 for GroundTheory.GroupCoh.hom_zero_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:49:33.632869+00:00
-- url     : https://prove2.me/submissions/59a48c55-39ad-4f46-80bf-fd765cb43508

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_PGroupCohTrivialInt
import Definitions.Def_GroundTheory_TateCohomology_Annihilation
import Definitions.Def_GroundTheory_TateCohomology_CohTrivialPGroup

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
open CategoryTheory Limits Rep
universe u
variable {k H : Type u} [CommRing k] [Group H] {A B : Rep.{u} k H}
namespace GroundTheory.GroupCoh
theorem _root_.solution (f : A ⟶ B) : f.hom 0 = 0 :=
  map_zero f.hom.toLinearMap
end GroundTheory.GroupCoh
