-- Prove2me | solution 1 for GlobalTheory.BI.virt_expand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:24:30.746852+00:00
-- url     : https://prove2.me/submissions/8fb7a75d-6ee6-4cc8-9b08-e45dd61089c6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldInductionIrreducibleStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FiniteGroupFunctionPairingSelfIrreducibleAlgClosStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_MemVirtualCharactersIffSubCharactersStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_StarVirtualCharacterEqApplyInvStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FiniteGroupFunctionPairingEqZeroOfDistinctIrreduStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_VirtualCharacterIrreducibleExpansionNormSq
import Theorems.Thm_GlobalTheory_BI_isChar_induction
import Theorems.Thm_GlobalTheory_BI_mem_virt_iff_sub
import Theorems.Thm_GlobalTheory_BI_pair_eq_zero_of_isIrrChar_ne
import Theorems.Thm_GlobalTheory_BI_pair_self_of_isIrrChar_algClosed
import Theorems.Thm_GlobalTheory_CuspGL_star_virt_eq_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
noncomputable section
namespace GlobalTheory.BI
open Polynomial in
private theorem exists_irreducible_expansion_of_isCharacter_lemma_3 {G : Type} [Group G] [Finite G]
    (a : G → ℂ) (ha : _root_.GlobalTheory.BI.IsChar ℂ ℂ a) :
    ∃ c : (G → ℂ) →₀ ℤ, (∀ χ ∈ c.support, _root_.GlobalTheory.BI.IsIrrChar ℂ ℂ χ) ∧
      a = c.sum (fun χ m => m • χ) := by
  classical
  refine _root_.GlobalTheory.BI.isChar_induction ℂ ℂ G
    (fun a => ∃ c : (G → ℂ) →₀ ℤ, (∀ χ ∈ c.support, _root_.GlobalTheory.BI.IsIrrChar ℂ ℂ χ) ∧
      a = c.sum (fun χ m => m • χ)) ⟨0, by simp, by simp⟩ ?_ a ha
  rintro φ b hφ - ⟨c, hc, rfl⟩
  refine ⟨Finsupp.single φ 1 + c, fun χ hχ => ?_, ?_⟩
  · rcases Finset.mem_union.1 (Finsupp.support_add hχ) with h | h
    · rw [Finsupp.mem_support_iff, Finsupp.single_apply] at h
      split_ifs at h with e
      · exact e ▸ hφ
      · exact absurd rfl h
    · exact hc χ h
  · rw [Finsupp.sum_add_index' (by simp) (fun _ _ _ => add_smul _ _ _),
      Finsupp.sum_single_index (by simp), one_smul]
open Polynomial in
private theorem exists_irreducible_expansion_of_mem_lemma {G : Type} [Group G] [Finite G]
    (φ : G → ℂ) (hφ : φ ∈ _root_.GlobalTheory.BI.Virt ℂ ℂ G) :
    ∃ c : (G → ℂ) →₀ ℤ, (∀ χ ∈ c.support, _root_.GlobalTheory.BI.IsIrrChar ℂ ℂ χ) ∧
      φ = c.sum (fun χ m => m • χ) := by
  classical
  obtain ⟨a, b, ha, hb, rfl⟩ := (_root_.GlobalTheory.BI.mem_virt_iff_sub ℂ ℂ G φ).1 hφ
  obtain ⟨ca, hca, rfl⟩ := exists_irreducible_expansion_of_isCharacter_lemma_3 a ha
  obtain ⟨cb, hcb, rfl⟩ := exists_irreducible_expansion_of_isCharacter_lemma_3 b hb
  refine ⟨ca - cb, fun χ hχ => ?_, ?_⟩
  · rcases Finset.mem_union.1 (Finsupp.support_sub hχ) with h | h
    · exact hca χ h
    · exact hcb χ h
  · rw [Finsupp.sum_sub_index (fun _ _ _ => sub_smul _ _ _)]
open Polynomial in
private theorem sum_mul_inv_irreducible_lemma_2 {G : Type} [Group G] [Fintype G] (χ ψ : G → ℂ)
    (hχ : _root_.GlobalTheory.BI.IsIrrChar ℂ ℂ χ) (hψ : _root_.GlobalTheory.BI.IsIrrChar ℂ ℂ ψ) :
    ∑ g, χ g * ψ g⁻¹ = if χ = ψ then (Nat.card G : ℂ) else 0 := by
  classical
  have hG : (Nat.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  split_ifs with h
  · subst h
    have := _root_.GlobalTheory.BI.pair_self_of_isIrrChar_algClosed ℂ G χ hχ
    unfold _root_.GlobalTheory.BI.pair at this
    rw [inv_mul_eq_one₀ hG, finsum_eq_sum_of_fintype] at this
    exact this.symm
  · have := _root_.GlobalTheory.BI.pair_eq_zero_of_isIrrChar_ne G χ ψ hχ hψ h
    unfold _root_.GlobalTheory.BI.pair at this
    rw [finsum_eq_sum_of_fintype] at this
    simpa [hG] using this
end GlobalTheory.BI
end
end

set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
noncomputable section
open GlobalTheory GlobalTheory.BI
open Polynomial
namespace GlobalTheory.BI
namespace _root_.GlobalTheory.BI
theorem _root_.solution : ∀ (G : Type) [Group G] [Finite G]
    (φ : G → ℂ), φ ∈ _root_.GlobalTheory.BI.Virt ℂ ℂ G →
    ∃ c : (G → ℂ) →₀ ℤ, (∀ χ ∈ c.support, _root_.GlobalTheory.BI.IsIrrChar ℂ ℂ χ) ∧
      φ = c.sum (fun χ m => m • χ) ∧
      ∑ᶠ g, φ g * star (φ g) = (c.sum fun _ m => (m : ℂ) ^ 2) * (Nat.card G : ℂ) := by
  intro G _ _ φ hφ
  classical
  haveI := Fintype.ofFinite G
  obtain ⟨c, hc, he⟩ := exists_irreducible_expansion_of_mem_lemma φ hφ
  refine ⟨c, hc, he, ?_⟩
  have hev : ∀ g, φ g = ∑ χ ∈ c.support, (c χ : ℂ) * χ g := by
    intro g
    rw [he, Finsupp.sum, Finset.sum_apply]
    simp [zsmul_eq_mul]
  rw [finsum_eq_sum_of_fintype]
  simp_rw [_root_.GlobalTheory.CuspGL.star_virt_eq_inv G φ hφ, hev, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  calc ∑ χ ∈ c.support, ∑ g, ∑ ψ ∈ c.support, (c χ : ℂ) * χ g * ((c ψ : ℂ) * ψ g⁻¹)
      = ∑ χ ∈ c.support, ∑ ψ ∈ c.support, (c χ : ℂ) * c ψ * ∑ g, χ g * ψ g⁻¹ := by
        refine Finset.sum_congr rfl fun χ _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun ψ _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun g _ => ?_
        ring
    _ = ∑ χ ∈ c.support, (c χ : ℂ) ^ 2 * (Nat.card G : ℂ) := by
        refine Finset.sum_congr rfl fun χ hχ => ?_
        rw [Finset.sum_congr rfl fun ψ hψ => by rw [sum_mul_inv_irreducible_lemma_2 χ ψ (hc χ hχ) (hc ψ hψ)]]
        simp only [mul_ite, mul_zero]
        rw [Finset.sum_ite_eq c.support χ, if_pos hχ]
        ring
    _ = _ := by rw [Finsupp.sum, Finset.sum_mul]
end _root_.GlobalTheory.BI
end GlobalTheory.BI
