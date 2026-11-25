-- Prove2me | solution 1 for GroundTheory.GroupCoh.tateAcyclic_free
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:43:57.98305+00:00
-- url     : https://prove2.me/submissions/fc4ece08-8aeb-4c1c-86cc-c50100341de1

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_Induced
import Definitions.Def_GroundTheory_TateCohomology_InducedNorm
import Theorems.Thm_GroundTheory_GroupCoh_tateAcyclic_leftRegular_tensor_trivial
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
open CategoryTheory Limits Rep MonoidalCategory
universe u
variable {k G : Type u} [CommRing k] [Group G] [Fintype G]
variable (B : Rep.{u} k G)
namespace GroundTheory.GroupCoh
theorem _root_.solution (α : Type u) : TateAcyclic (free k G α) := by
  classical
  exact (tateAcyclic_leftRegular_tensor_trivial _).of_iso (leftRegularTensorTrivialIsoFree k G α).symm
end GroundTheory.GroupCoh
