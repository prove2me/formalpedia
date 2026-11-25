-- Prove2me | solution 1 for GroundTheory.GroupCoh.norm_res_of_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:29:37.598857+00:00
-- url     : https://prove2.me/submissions/216c7357-0a01-4b96-9709-52fe0a51039c

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CohTrivialBasic
import Definitions.Def_GroundTheory_TateCohomology_TateLow
import Definitions.Def_GroundTheory_TateCohomology_TateGroupIso

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
theorem _root_.solution (B : Rep.{u} k K) (m : B) :
    (res f B).ρ.norm m = B.ρ.norm m := by
  rw [Representation.norm, Representation.norm, LinearMap.sum_apply, LinearMap.sum_apply]
  exact Fintype.sum_bijective f hf _ _ fun _ => rfl
end GroundTheory.GroupCoh
