-- Prove2me | solution 1 for GroundTheory.GroupCoh.tateAcyclic_ind_bot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:50:08.138847+00:00
-- url     : https://prove2.me/submissions/41c5d858-c2ce-4760-bcff-0b20c93cb0ad

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_Induced
import Theorems.Thm_GroundTheory_GroupCoh_isZero_tateCohomology_ind_bot

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
theorem _root_.solution : TateAcyclic (ind (⊥ : Subgroup G).subtype B) :=
  isZero_tateCohomology_ind_bot B
end GroundTheory.GroupCoh
