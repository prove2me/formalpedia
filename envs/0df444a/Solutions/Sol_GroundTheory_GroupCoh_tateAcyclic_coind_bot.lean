-- Prove2me | solution 1 for GroundTheory.GroupCoh.tateAcyclic_coind_bot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:36:06.692866+00:00
-- url     : https://prove2.me/submissions/a460095f-e31b-408c-88f0-6b707ec7b25c

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_Induced
import Theorems.Thm_GroundTheory_GroupCoh_isZero_tateCohomology_coind_bot

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
open CategoryTheory Limits groupCohomology groupHomology Rep
universe u
variable {k G : Type u} [CommRing k] [Group G] [Fintype G]
variable (B : Rep.{u} k (⊥ : Subgroup G))
namespace GroundTheory.GroupCoh
theorem _root_.solution : TateAcyclic (coind (⊥ : Subgroup G).subtype B) :=
  isZero_tateCohomology_coind_bot B
end GroundTheory.GroupCoh
