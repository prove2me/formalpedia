-- Prove2me | solution 1 for GroundTheory.GroupCoh.isZero_tateCohomology_ind_bot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:37:19.181896+00:00
-- url     : https://prove2.me/submissions/7c4ea21c-d3c6-4308-9936-6a140bcd86c4

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_Induced
import Theorems.Thm_GroundTheory_GroupCoh_TateAcyclic_of_iso
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
theorem _root_.solution (n : ℤ) :
    IsZero (tateCohomology (ind (⊥ : Subgroup G).subtype B) n) := by
  classical
  exact (isZero_tateCohomology_coind_bot B n).of_iso
    ((tateCohomologyFunctor n).mapIso (indCoindIso B))
end GroundTheory.GroupCoh
