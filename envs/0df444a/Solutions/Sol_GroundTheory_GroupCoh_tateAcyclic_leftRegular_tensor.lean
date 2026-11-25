-- Prove2me | solution 1 for GroundTheory.GroupCoh.tateAcyclic_leftRegular_tensor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:52:55.031044+00:00
-- url     : https://prove2.me/submissions/c15ed314-1c53-4baa-926b-7a457fd3c211

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_Induced
import Definitions.Def_GroundTheory_TateCohomology_InducedNorm
import Theorems.Thm_GroundTheory_GroupCoh_tateAcyclic_of_sum_eq
import Theorems.Thm_GroundTheory_GroupCoh_sum_leftRegular_tensor

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
theorem _root_.solution : TateAcyclic (leftRegular k G ⊗ B) :=
  tateAcyclic_of_sum_eq _ (TensorProduct.map coeffOneProj LinearMap.id) (sum_leftRegular_tensor B)
end GroundTheory.GroupCoh
