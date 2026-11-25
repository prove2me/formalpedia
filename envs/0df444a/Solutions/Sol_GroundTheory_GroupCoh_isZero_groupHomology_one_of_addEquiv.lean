-- Prove2me | solution 1 for GroundTheory.GroupCoh.isZero_groupHomology_one_of_addEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:47:48.196571+00:00
-- url     : https://prove2.me/submissions/602e4e24-6fce-4ad2-ab93-00ef12b75d37

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_PGroupCohTrivial
import Definitions.Def_GroundTheory_TateCohomology_TateAddEquivAbelianizationTateClass
import Definitions.Def_GroundTheory_TateCohomology_PGroupCohTrivialInt
import Theorems.Thm_GroundTheory_GroupCoh_isZero_groupHomology_one_iff
import Theorems.Thm_P2M_GroundTheory_GroupCoh_d___mapRange_addEquiv_855b748d2b6d
import Theorems.Thm_P2M_GroundTheory_GroupCoh_d___mapRange_addEquiv_c46ee4082a24
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
open CategoryTheory Limits Rep groupHomology
universe u
variable {k k' G : Type u} [CommRing k] [CommRing k'] [Group G]
variable {A : Rep.{u} k G} {B : Rep.{u} k' G}
namespace GroundTheory.GroupCoh
theorem _root_.solution (e : A.V ≃+ B.V)
    (he : ∀ g a, e (A.ρ g a) = B.ρ g (e a)) (h : IsZero (groupHomology A 1)) :
    IsZero (groupHomology B 1) := by
  rw [isZero_groupHomology_one_iff] at h ⊢
  intro y hy
  have hyy : Finsupp.mapRange e (map_zero e) (Finsupp.mapRange e.symm (map_zero e.symm) y) = y := by
    ext g; simp
  have hy' : d₁₀ A (Finsupp.mapRange e.symm (map_zero e.symm) y) = 0 := by
    apply e.injective
    rw [← d₁₀_mapRange_addEquiv e he, hyy, hy, map_zero]
  obtain ⟨c, hc⟩ := h _ hy'
  exact ⟨Finsupp.mapRange e (map_zero e) c, by rw [d₂₁_mapRange_addEquiv e he, hc, hyy]⟩
end GroundTheory.GroupCoh
