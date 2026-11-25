-- Prove2me | solution 1 for GroundTheory.GroupCoh.tateAcyclic_cohTrivial_of_isZero_of_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:04:17.360206+00:00
-- url     : https://prove2.me/submissions/6f2622b0-d39b-4741-ba6b-bd13cbb4abe2

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CohTrivialBasic
import Definitions.Def_GroundTheory_TateCohomology_PGroupFree
import Definitions.Def_GroundTheory_TateCohomology_PGroupCohTrivial
import Theorems.Thm_GroundTheory_GroupCoh_CohTrivial_of_iso
import Theorems.Thm_GroundTheory_GroupCoh_TateAcyclic_of_iso
import Theorems.Thm_GroundTheory_GroupCoh_cohTrivial_coind_bot
import Theorems.Thm_GroundTheory_GroupCoh_cohTrivial_ind_bot
import Theorems.Thm_P2M_GroundTheory_GroupCoh_CohTrivial_of_shortExact_X__518f55910066
import Theorems.Thm_P2M_GroundTheory_GroupCoh_CohTrivial_of_shortExact_X__9741d7cff3c2
import Theorems.Thm_P2M_GroundTheory_GroupCoh_TateAcyclic_of_shortExact_X__8e70e005e54b
import Theorems.Thm_P2M_GroundTheory_GroupCoh_TateAcyclic_of_shortExact_X__c00637e206cb
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
open scoped MonoidAlgebra
universe u
variable {k G : Type u} [CommRing k] [Group G] [Fintype G]
namespace GroundTheory.GroupCoh
theorem _root_.solution (P : Rep.{u} k G → Prop)
    (hcoind : ∀ M, P M → P (coindShift M)) (hind : ∀ M, P M → P (indShift M))
    (hbase : ∀ M, P M → IsZero (tateCohomology M (-2)) → TateAcyclic M ∧ CohTrivial M)
    (q : ℤ) (M : Rep.{u} k G) (hM : P M) (hq : IsZero (tateCohomology M q)) :
    TateAcyclic M ∧ CohTrivial M := by
  refine Int.inductionOn' (motive := fun q => ∀ M : Rep.{u} k G, P M →
    IsZero (tateCohomology M q) → TateAcyclic M ∧ CohTrivial M) q (-2) hbase ?_ ?_ M hM hq
  · intro n _ ih M hM hq
    have h1 : IsZero (tateCohomology (coindShift M) n) := hq.of_iso (coindShiftIso M n)
    obtain ⟨t, c⟩ := ih (coindShift M) (hcoind M hM) h1
    have hS := coindSES_shortExact M
    have t2 : TateAcyclic (coindSES.obj M).X₂ := tateAcyclic_coindSES_X₂ M
    have c2 : CohTrivial (coindSES.obj M).X₂ := by
      rw [coindSES_obj_X₂]; exact cohTrivial_coind_bot _
    have t1 := TateAcyclic.of_shortExact_X₃ hS t2 t
    have c1 := CohTrivial.of_shortExact_X₃ hS c2 c
    rw [coindSES_obj_X₁] at t1 c1
    exact ⟨t1, c1⟩
  · intro n _ ih M hM hq
    have h1 : IsZero (tateCohomology (indShift M) n) := by
      have h := hq.of_iso (indShiftIso M (n - 1)).symm
      rwa [sub_add_cancel] at h
    obtain ⟨t, c⟩ := ih (indShift M) (hind M hM) h1
    have hS := indSES_shortExact M
    have t2 : TateAcyclic (indSES.obj M).X₂ := tateAcyclic_indSES_X₂ M
    have c2 : CohTrivial (indSES.obj M).X₂ := by
      rw [indSES_obj_X₂]; exact cohTrivial_ind_bot _
    have t3 := TateAcyclic.of_shortExact_X₁ hS t2 t
    have c3 := CohTrivial.of_shortExact_X₁ hS c2 c
    rw [indSES_obj_X₃] at t3 c3
    exact ⟨t3, c3⟩
end GroundTheory.GroupCoh
