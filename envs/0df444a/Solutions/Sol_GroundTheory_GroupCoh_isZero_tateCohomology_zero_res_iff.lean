-- Prove2me | solution 1 for GroundTheory.GroupCoh.isZero_tateCohomology_zero_res_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:50:11.01678+00:00
-- url     : https://prove2.me/submissions/6f64c68f-4b72-4892-a2ca-6f623000ddd7

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CohTrivialBasic
import Definitions.Def_GroundTheory_TateCohomology_TateLow
import Definitions.Def_GroundTheory_TateCohomology_TateGroupIso
import Theorems.Thm_GroundTheory_GroupCoh_norm_res_of_bijective
import Theorems.Thm_GroundTheory_GroupCoh_indSES_obj_g
import Theorems.Thm_GroundTheory_GroupCoh_isZero_tateCohomology_zero_iff_forall
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
open CategoryTheory Limits Rep
universe u
variable {k H K : Type u} [CommRing k] [Group H] [Group K] [Fintype H] [Fintype K]
  (f : H →* K) (hf : Function.Bijective f)
include hf
namespace GroundTheory.GroupCoh
theorem _root_.solution (B : Rep.{u} k K) :
    IsZero (tateCohomology (res f B) 0) ↔ IsZero (tateCohomology B 0) := by
  rw [isZero_tateCohomology_zero_iff_forall, isZero_tateCohomology_zero_iff_forall]
  have hinv : ∀ x : B, x ∈ (res f B).ρ.invariants ↔ x ∈ B.ρ.invariants := fun x => by
    simp only [Representation.mem_invariants]
    constructor
    · intro h g
      obtain ⟨h', rfl⟩ := hf.2 g
      exact h h'
    · intro h h'
      exact h (f h')
  constructor
  · intro h x hx
    obtain ⟨m, hm⟩ := h x ((hinv x).2 hx)
    exact ⟨m, by rw [← norm_res_of_bijective f hf]; exact hm⟩
  · intro h x hx
    obtain ⟨m, hm⟩ := h x ((hinv x).1 hx)
    exact ⟨m, by rw [norm_res_of_bijective f hf]; exact hm⟩
end GroundTheory.GroupCoh
