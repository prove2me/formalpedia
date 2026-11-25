-- Prove2me | solution 1 for GlobalTheory.BI.irr_of_norm_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:46:26.298514+00:00
-- url     : https://prove2.me/submissions/dc2fa0c8-e991-4c67-9b97-88d10622d949

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldRestrictClassFunctionOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_VirtualCharacterIrreducibleExpansionNormSqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IrreducibleOfVirtualCharacterNormOne
import Theorems.Thm_GlobalTheory_BI_finsupp_eq_single_of_sum_sq_eq_one
import Theorems.Thm_GlobalTheory_T_virtualCharacter_irreducible_expansion_normSq
import Theorems.Thm_GlobalTheory_isChar_restrict_conj_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
namespace GlobalTheory.BI
private theorem exists_pos_nat_apply_one_of_isIrrChar {G : Type} [Group G] (χ : G → ℂ) (h : IsIrrChar ℂ ℂ χ) :
    ∃ n : ℕ, 0 < n ∧ χ 1 = n := by
  obtain ⟨n, ρ, hρ, hχ⟩ := h
  refine ⟨n, ?_, ?_⟩
  · have hs : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule :=
      (Representation.irreducible_iff_isSimpleModule_asModule ρ).mp hρ
    have hnt : Nontrivial ρ.asModule := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) _
    rcases Nat.eq_zero_or_pos n with h0 | hn
    · exfalso
      subst h0
      obtain ⟨x, y, hxy⟩ := hnt
      exact hxy (Subsingleton.elim (α := Fin 0 → ℂ) x y)
    · exact hn
  · rw [hχ, Representation.char_one]
    simp
end GlobalTheory.BI
end

set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory GlobalTheory.BI
namespace GlobalTheory.BI
theorem _root_.solution : ∀ (G : Type) [Group G] [Finite G] (φ : G → ℂ), φ ∈ Virt ℂ ℂ G → ∑ᶠ g, φ g * star (φ g) = (Nat.card G : ℂ) → (IsIrrChar ℂ ℂ φ ∨ IsIrrChar ℂ ℂ (-φ)) ∧ (IsChar ℂ ℂ φ → IsIrrChar ℂ ℂ φ ∧ ∃ n : ℕ, 0 < n ∧ φ 1 = n) := by
  intro G _ _ φ hφ hnorm
  obtain ⟨c, hirr, hsum, hsq⟩ := GlobalTheory.T.virtualCharacter_irreducible_expansion_normSq G φ hφ
  have hG : (Nat.card G : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have h1 : (c.sum fun _ m => (m : ℂ) ^ 2) = 1 :=
    mul_right_cancel₀ hG ((hsq.symm.trans hnorm).trans (one_mul _).symm)
  have h2 : (c.sum fun _ m => m ^ 2) = 1 := by
    simp only [Finsupp.sum] at h1 ⊢
    exact_mod_cast h1
  obtain ⟨χ, hsupp, hc⟩ := finsupp_eq_single_of_sum_sq_eq_one c h2
  have hχ : IsIrrChar ℂ ℂ χ := hirr χ (by rw [hsupp]; exact Finset.mem_singleton_self χ)
  have hφχ : φ = c χ • χ := by
    rw [hsum, Finsupp.sum, hsupp, Finset.sum_singleton]
  have key : φ = χ ∨ φ = -χ := by
    rcases hc with h | h
    · left
      rw [hφχ, h, one_smul]
    · right
      rw [hφχ, h, neg_smul, one_smul]
  obtain ⟨n, hn, hn1⟩ := exists_pos_nat_apply_one_of_isIrrChar χ hχ
  rcases key with rfl | rfl
  · exact ⟨Or.inl hχ, fun _ => ⟨hχ, n, hn, hn1⟩⟩
  · refine ⟨Or.inr (by simpa using hχ), fun hc' => ?_⟩
    exfalso
    obtain ⟨-, -, m, hm, -⟩ := GlobalTheory.isChar_restrict_conj_one ℂ ℂ G (-χ) hc'
    have h3 : ((m + n : ℕ) : ℂ) = 0 := by
      push_cast
      rw [← hm, ← hn1, Pi.neg_apply]
      ring
    have h4 : m + n = 0 := by exact_mod_cast h3
    omega
end GlobalTheory.BI
