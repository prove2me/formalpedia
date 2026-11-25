-- Prove2me | solution 1 for GroundTheory.ProfCoh.coprime_card_coprimeRelPreimage
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:24:40.62571+00:00
-- url     : https://prove2.me/submissions/9012fbe9-fd48-4860-aa4b-35a3decf4c58

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_GroupStructureDefs
import Definitions.Def_GroundTheory_LocalFields_RamificationStructure
import Definitions.Def_GroundTheory_LocalFields_UnramifiedRootsOfUnity
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_GroupStructure
import Theorems.Thm_GroundTheory_ProfCoh_mem_coprimePart_iff_of_comm
import Theorems.Thm_GroundTheory_ProfCoh_eq_one_of_pow_eq_one_of_coprime
import Theorems.Thm_GroundTheory_ProfCoh_coprime_card_of_pow_eq_one
import Theorems.Thm_GroundTheory_LocalField_ramificationQuotientToUnits_mk
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.ramificationQuotientToUnits_mk
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
variable {G : Type*} [Group G]
variable (N : Subgroup G) [N.Normal]
variable (G₀ G₁ : Subgroup G) [G₁.Normal]
namespace GroundTheory.ProfCoh
theorem _root_.solution [Finite G] {l p : ℕ} (hl : l.Prime) (hp : p.Prime)
    (hlp : l ≠ p) (hG1 : IsPGroup p G₁) [IsCyclic (G₀ ⧸ G₁.subgroupOf G₀)] :
    (Nat.card (coprimeRelPreimage G₀ G₁ l)).Coprime l := by
  have := Fact.mk hl
  apply coprime_card_of_pow_eq_one
  rintro ⟨b, hb⟩ hbl
  have hbl' : b ^ l = 1 := by
    simpa using congrArg Subtype.val hbl
  obtain ⟨hb0, hb'⟩ := (mem_coprimeRelPreimage_iff G₀ G₁).1 hb
  have hcomm : ∀ a c : G₀ ⧸ G₁.subgroupOf G₀, a * c = c * a :=
    fun a c ↦ (IsCyclic.commGroup).mul_comm a c
  rw [mem_coprimePart_iff_of_comm hcomm] at hb'
  have h1 := eq_one_of_pow_eq_one_of_coprime hb' (by
    rw [← QuotientGroup.mk_pow, show (⟨b, hb0⟩ : G₀) ^ l = 1 from Subtype.ext (by simpa using hbl'),
      QuotientGroup.mk_one])
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
  obtain ⟨k, hk⟩ := hG1 ⟨b, h1⟩
  have hbk : b ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hco : (orderOf b).Coprime l :=
    Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hbk)
      (Nat.Coprime.pow_left k ((Nat.coprime_primes hp hl).2 hlp.symm))
  exact Subtype.ext (eq_one_of_pow_eq_one_of_coprime hco hbl')
end GroundTheory.ProfCoh
