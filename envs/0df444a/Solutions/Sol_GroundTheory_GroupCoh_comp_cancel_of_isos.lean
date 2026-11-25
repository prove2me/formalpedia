-- Prove2me | solution 1 for GroundTheory.GroupCoh.comp_cancel_of_isos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:10:45.831834+00:00
-- url     : https://prove2.me/submissions/d340e40d-79bd-497c-a5c8-bbbc0992fd74

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_ResCores
import Definitions.Def_GroundTheory_TateCohomology_ResCoresPos
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
open GroundTheory GroundTheory.GroupCoh
open CategoryTheory Limits Rep groupCohomology
universe u
namespace GroundTheory.GroupCoh
theorem _root_.solution {C : Type*} [Category C] {X X' Y Y' Z Z' : C} (pG : X ≅ X') (pS : Y ≅ Y')
    (pGc : Z ≅ Z') (a : X ⟶ Z) (cu : X' ⟶ Z') (m : X' ⟶ Y') (sh : Y' ⟶ Z') (b : Y ⟶ Z) (c : Z ⟶ Y)
    (ha : a = pG.hom ≫ cu ≫ pGc.inv) (hcu : cu = m ≫ sh) (hsh : sh = pS.inv ≫ b ≫ pGc.hom)
    (hb : b ≫ c = 𝟙 Y) : a ≫ c ≫ pS.hom = pG.hom ≫ m := by
  subst ha hcu hsh
  simp [reassoc_of% hb]
end GroundTheory.GroupCoh
