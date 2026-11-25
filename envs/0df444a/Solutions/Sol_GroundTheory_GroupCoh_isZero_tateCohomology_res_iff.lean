-- Prove2me | solution 1 for GroundTheory.GroupCoh.isZero_tateCohomology_res_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:33:32.176051+00:00
-- url     : https://prove2.me/submissions/e75b70be-0aaf-4ada-a2ed-6cdad6126ea2

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CohTrivialBasic
import Definitions.Def_GroundTheory_TateCohomology_TateLow
import Definitions.Def_GroundTheory_TateCohomology_TateGroupIso
import Theorems.Thm_GroundTheory_GroupCoh_isZero_tateCohomology_zero_res_iff
import Theorems.Thm_GroundTheory_GroupCoh_tateAcyclic_res_of_sum_eq
import Theorems.Thm_GroundTheory_GroupCoh_CohTrivial_of_iso
import Theorems.Thm_GroundTheory_GroupCoh_TateAcyclic_of_iso
import Theorems.Thm_GroundTheory_GroupCoh_sum_coindBotProj
import Theorems.Thm_P2M_GroundTheory_GroupCoh_indSES_obj_X__c57492aa2d98
import Theorems.Thm_P2M_GroundTheory_GroupCoh_indSES_obj_X__e6c60d2b2881
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_GroupCoh_indSES_obj_X__c57492aa2d98
attribute [local simp] P2M_GroundTheory_GroupCoh_indSES_obj_X__e6c60d2b2881



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.GroupCoh
open CategoryTheory Limits Rep
universe u
variable {k H K : Type u} [CommRing k] [Group H] [Group K] [Fintype H] [Fintype K]
  (f : H →* K) (hf : Function.Bijective f)
include hf
namespace GroundTheory.GroupCoh
theorem _root_.solution (n : ℤ) (B : Rep.{u} k K) :
    IsZero (tateCohomology (res f B) n) ↔ IsZero (tateCohomology B n) := by
  refine Int.inductionOn' (motive := fun n => ∀ B : Rep.{u} k K,
    IsZero (tateCohomology (res f B) n) ↔ IsZero (tateCohomology B n)) n 0
    (fun B => isZero_tateCohomology_zero_res_iff f hf B) ?_ ?_ B
  · intro n _ ih B
    have hX' : ((coindSES.obj B).map (resFunctor f)).ShortExact :=
      (shortExact_res f).2 (coindSES_shortExact B)
    have h2 : TateAcyclic ((coindSES.obj B).map (resFunctor f)).X₂ := by
      rw [ShortComplex.map_X₂, coindSES_obj_X₂]
      exact tateAcyclic_res_of_sum_eq f hf _ (coindBotProj _) (sum_coindBotProj _)
    have e1 := @asIso _ _ _ _ (TateCohomology.δ hX' n) (isIso_δ_of_tateAcyclic hX' h2 n)
    rw [ShortComplex.map_X₃, ShortComplex.map_X₁, coindSES_obj_X₁] at e1
    rw [← e1.isZero_iff, ← (coindShiftIso B n).isZero_iff]
    exact ih _
  · intro n _ ih B
    have hX' : ((indSES.obj B).map (resFunctor f)).ShortExact :=
      (shortExact_res f).2 (indSES_shortExact B)
    have h2 : TateAcyclic ((indSES.obj B).map (resFunctor f)).X₂ := by
      classical
      rw [ShortComplex.map_X₂, indSES_obj_X₂]
      exact (tateAcyclic_res_of_sum_eq f hf _ (coindBotProj _) (sum_coindBotProj _)).of_iso
        ((resFunctor f).mapIso (indCoindIso _))
    have e1 := @asIso _ _ _ _ (TateCohomology.δ hX' (n - 1))
      (isIso_δ_of_tateAcyclic hX' h2 (n - 1))
    rw [ShortComplex.map_X₃, ShortComplex.map_X₁, indSES_obj_X₃] at e1
    rw [e1.isZero_iff, (indShiftIso B (n - 1)).isZero_iff, sub_add_cancel]
    exact ih _
end GroundTheory.GroupCoh
