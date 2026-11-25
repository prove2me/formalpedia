-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.mem_zpowers_sup_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:15:07.68928+00:00
-- url     : https://prove2.me/submissions/c27e42ab-7ade-42e4-b1fc-7471f68e8297

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsEqNsmulOfProjEqZero
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Valuation
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Frobenius

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField GroundTheory.LocalField.Abstract
open ProfiniteInteger
variable {G : Type*} [Group G] {d : G →* Multiplicative ℤ̂} {L : Subgroup G} {σ : G}
namespace GroundTheory.LocalField.Abstract
theorem _root_.solution (hσ : σ ∈ Subgroup.normalizer ((L ⊓ d.ker : Subgroup G) : Set G))
    {h : G} : h ∈ Subgroup.zpowers σ ⊔ (L ⊓ d.ker) ↔ ∃ k : ℤ, ∃ j ∈ L ⊓ d.ker, h = σ ^ k * j := by
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _
    (Subgroup.zpowers_le.2 hσ), Set.mem_mul]
  constructor
  · rintro ⟨a, ha, j, hj, rfl⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    exact ⟨k, j, hj, rfl⟩
  · rintro ⟨k, j, hj, rfl⟩
    exact ⟨σ ^ k, Subgroup.zpow_mem_zpowers σ k, j, hj, rfl⟩
end GroundTheory.LocalField.Abstract
