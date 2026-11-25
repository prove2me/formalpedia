-- Prove2me | solution 1 for GroundTheory.GroupCoh.tateAcyclic_leftRegular
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:28:00.143851+00:00
-- url     : https://prove2.me/submissions/f25848a2-9fb6-4b38-83df-ad4cff9516e8

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_Induced
import Definitions.Def_GroundTheory_TateCohomology_InducedNorm
import Theorems.Thm_GroundTheory_GroupCoh_tateAcyclic_leftRegular_tensor
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
theorem _root_.solution : TateAcyclic (leftRegular k G) :=
  (tateAcyclic_leftRegular_tensor (𝟙_ (Rep k G))).of_iso (ρ_ (leftRegular k G)).symm
end GroundTheory.GroupCoh
