-- Prove2me | solution 1 for GroundTheory.GroupCoh.res_res
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:28:06.168813+00:00
-- url     : https://prove2.me/submissions/8d9b3625-a33e-494a-8d36-acda8255e21b

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
variable {k G : Type u} [CommRing k] [Group G]
omit [Group G]
namespace GroundTheory.GroupCoh
theorem _root_.solution {H K : Type u} [Group H] [Group K] [Group G] (f : H →* K) (g : K →* G)
    (A : Rep.{u} k G) : res f (res g A) = res (g.comp f) A :=
  rfl
end GroundTheory.GroupCoh
