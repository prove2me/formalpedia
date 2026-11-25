-- Prove2me | solution 1 for GroundTheory.GroupCoh.tateRes_tateZeroClass
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:23:39.06572+00:00
-- url     : https://prove2.me/submissions/aa52e201-a8ed-4a92-854e-11d55186de9e

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CoresRes
import Definitions.Def_GroundTheory_TateCohomology_TateZeroClass
import Definitions.Def_GroundTheory_TateCohomology_ResCoresZero
import Theorems.Thm_GroundTheory_GroupCoh_coe_transferInv
import Theorems.Thm_GroundTheory_GroupCoh_coindConst_apply
import Theorems.Thm_GroundTheory_GroupCoh_tateCoindIso_hom_tateZeroClass
import Theorems.Thm_GroundTheory_GroupCoh_indSES_obj_g
import Theorems.Thm_GroundTheory_GroupCoh_tateCohomologyFunctor_map_tateZeroClass
import Theorems.Thm_GroundTheory_GroupCoh_tateRes_app
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


attribute [local simp] GroundTheory.GroupCoh.coe_transferInv
attribute [local simp] GroundTheory.GroupCoh.coindConst_apply

set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.GroupCoh
open CategoryTheory Limits Rep groupCohomology
universe u
variable {k G : Type u} [CommRing k] [Group G] [Fintype G] (S : Subgroup G) [Fintype S]
namespace GroundTheory.GroupCoh
theorem _root_.solution (A : Rep.{u} k G) (x : A.ρ.invariants) :
    ((tateRes S 0).app A).hom (tateZeroClass A x) =
      tateZeroClass (res S.subtype A) (invariantsRes S.subtype x) := by
  rw [tateRes_app, ModuleCat.hom_comp, LinearMap.comp_apply]
  erw [tateCohomologyFunctor_map_tateZeroClass]
  have h : ((Rep.invariantsFunctor k G).map
      ((Rep.resCoindAdjunction.{u, u} k S.subtype).unit.app A)).hom x =
      coindConst S (res S.subtype A) (invariantsRes S.subtype x) :=
    Subtype.ext (Subtype.ext (funext fun g => x.2 g))
  rw [h]
  exact tateCoindIso_hom_tateZeroClass S (res S.subtype A) (invariantsRes S.subtype x)
end GroundTheory.GroupCoh
