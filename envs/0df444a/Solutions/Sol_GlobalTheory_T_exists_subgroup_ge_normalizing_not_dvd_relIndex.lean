-- Prove2me | solution 1 for GlobalTheory.T.exists_subgroup_ge_normalizing_not_dvd_relIndex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:55:18.616359+00:00
-- url     : https://prove2.me/submissions/57876581-4684-4fd7-8c8c-0261ab4fd01d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsSylowOverSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsSylowOverSubgroupStatement
import Theorems.Thm_GlobalTheory_exists_sylow_over_subgroup


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (G : Type) [Group G] [Finite G] (C : Subgroup G) (p : ℕ), p.Prime → ∃ H : Subgroup G, C ≤ H ∧ (∀ h ∈ H, ∀ c ∈ C, h * c * h⁻¹ ∈ C) ∧ (∀ h ∈ H, ∃ k : ℕ, h ^ p ^ k ∈ C) ∧ ∀ N : Subgroup G, (∀ g : G, g ∈ N ↔ ∀ c ∈ C, g * c * g⁻¹ ∈ C) → ¬ p ∣ H.relIndex N := by
  first | exact @GlobalTheory.exists_sylow_over_subgroup | exact GlobalTheory.exists_sylow_over_subgroup | (intros; apply GlobalTheory.exists_sylow_over_subgroup <;> assumption)
end _root_.GlobalTheory.T
