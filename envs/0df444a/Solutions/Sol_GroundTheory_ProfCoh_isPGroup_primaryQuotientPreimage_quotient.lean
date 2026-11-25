-- Prove2me | solution 1 for GroundTheory.ProfCoh.isPGroup_primaryQuotientPreimage_quotient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:24:44.084875+00:00
-- url     : https://prove2.me/submissions/d97665c5-76a5-4507-a044-28fb5b6a594e

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_GroupStructureDefs
import Definitions.Def_GroundTheory_LocalFields_RamificationStructure
import Definitions.Def_GroundTheory_LocalFields_UnramifiedRootsOfUnity
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_GroupStructure
import Theorems.Thm_GroundTheory_ProfCoh_mem_primaryPart_iff_of_comm
import Theorems.Thm_GroundTheory_ProfCoh_exists_pow_prime_pow_mem_coprimePart

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
variable (G₀ G₁ : Subgroup G) [G₁.Normal]
variable [G₀.Normal]
namespace GroundTheory.ProfCoh
theorem _root_.solution [Finite G] {l : ℕ} (hl : l.Prime)
    [IsCyclic (G ⧸ G₀)] :
    IsPGroup l (primaryQuotientPreimage G₀ l ⧸
      (coprimeRelPreimage G₀ G₁ l).subgroupOf (primaryQuotientPreimage G₀ l)) := by
  intro y
  obtain ⟨⟨a, ha⟩, rfl⟩ := QuotientGroup.mk_surjective y
  have hcomm : ∀ a b : G ⧸ G₀, a * b = b * a := fun a b ↦ (IsCyclic.commGroup).mul_comm a b
  rw [primaryQuotientPreimage, Subgroup.mem_comap, mem_primaryPart_iff_of_comm hl hcomm] at ha
  obtain ⟨n, hn⟩ := ha
  have ha0 : a ^ l ^ n ∈ G₀ := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, ← QuotientGroup.mk'_apply, ← hn,
      pow_orderOf_eq_one]
  obtain ⟨k, hk⟩ := exists_pow_prime_pow_mem_coprimePart hl
    (isOfFinOrder_of_finite (QuotientGroup.mk (⟨a ^ l ^ n, ha0⟩ : G₀) : G₀ ⧸ G₁.subgroupOf G₀))
  have hB : (a ^ l ^ n) ^ l ^ k ∈ coprimeRelPreimage G₀ G₁ l := by
    refine (mem_coprimeRelPreimage_iff G₀ G₁).2 ⟨pow_mem ha0 _, ?_⟩
    rw [← QuotientGroup.mk_pow] at hk
    exact hk
  refine ⟨n + k, ?_⟩
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.coe_pow,
    pow_add, pow_mul]
  exact hB
end GroundTheory.ProfCoh
