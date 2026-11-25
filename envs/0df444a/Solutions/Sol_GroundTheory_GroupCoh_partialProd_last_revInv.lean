-- Prove2me | solution 1 for GroundTheory.GroupCoh.partialProd_last_revInv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:49:04.841855+00:00
-- url     : https://prove2.me/submissions/2735c48e-eef9-4493-9aac-ad4d8fca6949

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_DimensionShift
import Definitions.Def_GroundTheory_TateCohomology_CochainReverse
import Theorems.Thm_GroundTheory_GroupCoh_indSES_obj_g
import Theorems.Thm_P2M_GroundTheory_GroupCoh_indSES_map____b9067ca7808e
import Theorems.Thm_P2M_GroundTheory_GroupCoh_indSES_obj_X__c57492aa2d98
import Theorems.Thm_P2M_GroundTheory_GroupCoh_indSES_obj_X__e6c60d2b2881
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.GroupCoh.indSES_obj_g
attribute [local simp] P2M_GroundTheory_GroupCoh_indSES_map____b9067ca7808e
attribute [local simp] P2M_GroundTheory_GroupCoh_indSES_obj_X__c57492aa2d98
attribute [local simp] P2M_GroundTheory_GroupCoh_indSES_obj_X__e6c60d2b2881



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
universe u
open CategoryTheory Limits groupCohomology
open GroundTheory GroundTheory.GroupCoh
variable {G : Type*} [Group G] {n : ℕ}
namespace GroundTheory.GroupCoh
theorem _root_.solution (x : Fin n → G) :
    Fin.partialProd (revInv x) (Fin.last n) = (Fin.partialProd x (Fin.last n))⁻¹ := by
  induction n with
  | zero => simp [show Fin.last 0 = 0 from rfl]
  | succ n ih =>
    have h1 := Fin.partialProd_succ (revInv x) (Fin.last n)
    have h2 := Fin.partialProd_succ' x (Fin.last n)
    rw [Fin.succ_last] at h1 h2
    rw [h1, h2, ← Fin.partialProd_init]
    have : Fin.init (revInv x) = revInv (Fin.tail x) := by
      funext i
      simp only [Fin.init, Fin.tail, revInv_apply]
      congr 2
      ext
      simp only [Fin.val_rev, Fin.val_succ, Fin.val_castSucc]
      omega
    rw [this, ih, revInv_apply, mul_inv_rev, Fin.rev_last]
end GroundTheory.GroupCoh
