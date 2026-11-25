-- Prove2me | solution 1 for GroundTheory.LocalField.StableFiltration.subsingleton_tateNegOne_gr_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:23:30.34118+00:00
-- url     : https://prove2.me/submissions/9e85c948-cb90-4357-8660-135d18521c09

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj
import Definitions.Def_GroundTheory_LocalFields_CompleteTrivial
import Theorems.Thm_GroundTheory_LocalField_augmentation_eq_range
import Theorems.Thm_GroundTheory_LocalField_subsingleton_tateNegOne_iff
import Theorems.Thm_GroundTheory_LocalField_StableFiltration_grMk_eq_one_iff
import Theorems.Thm_GroundTheory_LocalField_StableFiltration_grMk_eq_grMk_iff
import Theorems.Thm_GroundTheory_LocalField_StableFiltration_coe_tateNorm_F
import Theorems.Thm_GroundTheory_LocalField_StableFiltration_coe_augMap_F
import Theorems.Thm_GroundTheory_LocalField_StableFiltration_tateNorm_grMk
import Theorems.Thm_GroundTheory_LocalField_StableFiltration_augMap_grMk

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField
open Finset Filter
open GroundTheory.LocalField.StableFiltration
variable {G V : Type*} [Group G] [CommGroup V] [MulDistribMulAction G V]
  (S : StableFiltration G V)
variable [Fintype G]
namespace GroundTheory.LocalField.StableFiltration
theorem _root_.solution (n : ℕ) :
    Subsingleton (TateNegOne G (S.gr n)) ↔
      ∀ x ∈ S.F n, tateNorm G V x ∈ S.F (n + 1) →
        ∃ m : G → V, (∀ g, m g ∈ S.F n) ∧ x / augMap G V m ∈ S.F (n + 1) := by
  rw [subsingleton_tateNegOne_iff, augmentation_eq_range]
  constructor
  · intro h x hx hN
    obtain ⟨q, hq⟩ := h (S.grMk n ⟨x, hx⟩) (by
      rw [tateNorm_grMk, grMk_eq_one_iff, coe_tateNorm_F]
      exact hN)
    have hl : ∀ g, ∃ y, S.grMk n y = q g := fun g => S.grMk_surjective n (q g)
    choose m hm using hl
    have e : q = fun g => S.grMk n (m g) := funext fun g => (hm g).symm
    rw [e, augMap_grMk, eq_comm, grMk_eq_grMk_iff, coe_augMap_F] at hq
    exact ⟨fun g => (m g : V), fun g => (m g).2, hq⟩
  · intro h q hq
    obtain ⟨x, rfl⟩ := S.grMk_surjective n q
    rw [tateNorm_grMk, grMk_eq_one_iff, coe_tateNorm_F] at hq
    obtain ⟨m, hm, hxm⟩ := h x x.2 hq
    refine ⟨fun g => S.grMk n ⟨m g, hm g⟩, ?_⟩
    rw [augMap_grMk, eq_comm, grMk_eq_grMk_iff, coe_augMap_F]
    exact hxm
end GroundTheory.LocalField.StableFiltration
