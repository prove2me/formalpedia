-- Prove2me | solution 1 for GroundTheory.GroupCoh.repSubOne_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:10:47.063438+00:00
-- url     : https://prove2.me/submissions/91ab742f-4124-428c-ac42-79f4472e7065

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Definitions.Def_GroundTheory_TateCohomology_HerbrandRep

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
universe w u v
variable {k : Type u} {G : Type v} [CommRing k] [Group G]
namespace GroundTheory.GroupCoh
theorem _root_.solution (A : Rep.{w} k G) (σ : G) (x : A) : repSubOne A σ x = A.ρ σ x - x :=
  rfl
end GroundTheory.GroupCoh
