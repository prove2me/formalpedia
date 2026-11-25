-- Prove2me | solution 1 for GroundTheory.ProfCoh.coprime_card_coprimeQuotientPreimage_quotient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:24:04.682552+00:00
-- url     : https://prove2.me/submissions/ba13c71d-d779-45c0-9d72-f1a642d9d8d2

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_GroupStructureDefs
import Definitions.Def_GroundTheory_LocalFields_RamificationStructure
import Definitions.Def_GroundTheory_LocalFields_UnramifiedRootsOfUnity
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_GroupStructure
import Theorems.Thm_GroundTheory_ProfCoh_mem_coprimePart_iff_of_comm
import Theorems.Thm_GroundTheory_ProfCoh_eq_one_of_pow_eq_one_of_coprime
import Theorems.Thm_GroundTheory_ProfCoh_coprime_card_of_pow_eq_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
variable {G : Type*} [Group G]
variable (N : Subgroup G) [N.Normal]
namespace GroundTheory.ProfCoh
theorem _root_.solution [Finite G] {p : ℕ} (hp : p.Prime)
    (G₀ G₁ : Subgroup G) [G₀.Normal] [G₁.Normal] (h10 : G₁ ≤ G₀) [IsCyclic (G ⧸ G₀)]
    (hG0 : (Nat.card (G₀ ⧸ G₁.subgroupOf G₀)).Coprime p) :
    (Nat.card (coprimeQuotientPreimage G₀ p ⧸
      G₁.subgroupOf (coprimeQuotientPreimage G₀ p))).Coprime p := by
  have := Fact.mk hp
  apply coprime_card_of_pow_eq_one
  intro y hy
  obtain ⟨⟨h, hH⟩, rfl⟩ := QuotientGroup.mk_surjective y
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
    Subgroup.coe_pow] at hy
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hcomm : ∀ a b : G ⧸ G₀, a * b = b * a := fun a b ↦ (IsCyclic.commGroup).mul_comm a b
  have h0 : h ∈ G₀ := by
    rw [coprimeQuotientPreimage, Subgroup.mem_comap, mem_coprimePart_iff_of_comm hcomm] at hH
    have h1 := eq_one_of_pow_eq_one_of_coprime hH (by
      rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact h10 hy)
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  have h1 := eq_one_of_pow_eq_one_of_coprime
    (x := (QuotientGroup.mk (⟨h, h0⟩ : G₀) : G₀ ⧸ G₁.subgroupOf G₀))
    (Nat.Coprime.coprime_dvd_left (orderOf_dvd_natCard _) hG0) (by
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
        Subgroup.coe_pow]
      exact hy)
  rwa [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
end GroundTheory.ProfCoh
