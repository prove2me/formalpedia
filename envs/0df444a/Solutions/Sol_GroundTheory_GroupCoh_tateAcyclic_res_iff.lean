-- Prove2me | solution 1 for GroundTheory.GroupCoh.tateAcyclic_res_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:17:14.395238+00:00
-- url     : https://prove2.me/submissions/e7278be6-0bc3-46bc-a2f1-780d0e2bcf49

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CohTrivialBasic
import Definitions.Def_GroundTheory_TateCohomology_TateLow
import Definitions.Def_GroundTheory_TateCohomology_TateGroupIso
import Theorems.Thm_GroundTheory_GroupCoh_isZero_tateCohomology_res_iff

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
variable {k H K : Type u} [CommRing k] [Group H] [Group K] [Fintype H] [Fintype K]
  (f : H →* K) (hf : Function.Bijective f)
include hf
namespace GroundTheory.GroupCoh
theorem _root_.solution (B : Rep.{u} k K) : TateAcyclic (res f B) ↔ TateAcyclic B :=
  forall_congr' fun n => isZero_tateCohomology_res_iff f hf n B
end GroundTheory.GroupCoh
