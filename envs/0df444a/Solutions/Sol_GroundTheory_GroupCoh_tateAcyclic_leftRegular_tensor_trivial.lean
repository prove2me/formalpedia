-- Prove2me | solution 1 for GroundTheory.GroupCoh.tateAcyclic_leftRegular_tensor_trivial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:28:01.00998+00:00
-- url     : https://prove2.me/submissions/7fa6f08c-1425-49cb-86ae-636e6144206f

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_Induced
import Definitions.Def_GroundTheory_TateCohomology_InducedNorm
import Theorems.Thm_GroundTheory_GroupCoh_tateAcyclic_leftRegular_tensor

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
theorem _root_.solution (V : Type u) [AddCommGroup V] [Module k V] :
    TateAcyclic (leftRegular k G ⊗ trivial k G V) :=
  tateAcyclic_leftRegular_tensor _
end GroundTheory.GroupCoh
