-- Prove2me | solution 1 for GroundTheory.GroupCoh.cohTrivial_ind_bot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:13:38.513003+00:00
-- url     : https://prove2.me/submissions/6b9035b7-681a-44dc-9302-6f9606903ff1

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_DimensionShift
import Definitions.Def_GroundTheory_TateCohomology_InducedNorm
import Definitions.Def_GroundTheory_TateCohomology_CoindOne
import Definitions.Def_GroundTheory_TateCohomology_UniquelyDivisible
import Definitions.Def_GroundTheory_TateCohomology_CohTrivialBasic
import Theorems.Thm_GroundTheory_GroupCoh_CohTrivial_of_iso
import Theorems.Thm_GroundTheory_GroupCoh_cohTrivial_coind_bot
import Theorems.Thm_GroundTheory_GroupCoh_TateAcyclic_of_iso


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
open scoped MonoidAlgebra
universe u
variable {k G : Type u} [CommRing k] [Group G]
variable {V : Type*} [AddCommGroup V] [Module k V]
variable [Fintype G]
namespace GroundTheory.GroupCoh
theorem _root_.solution (B : Rep.{u} k (⊥ : Subgroup G)) :
    CohTrivial (ind (⊥ : Subgroup G).subtype B) := by
  classical
  exact (cohTrivial_coind_bot B).of_iso (indCoindIso B)
end GroundTheory.GroupCoh
