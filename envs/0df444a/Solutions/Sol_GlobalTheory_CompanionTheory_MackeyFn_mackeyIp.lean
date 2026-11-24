-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.MackeyFn.mackeyIp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:41:38.343709+00:00
-- url     : https://prove2.me/submissions/0fd724fa-350d-4cb1-8091-e0bbb4e47aee

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MackeyInnerProduct
import Theorems.Thm_GlobalTheory_CompanionTheory_MackeyFn_ip_inter
import Theorems.Thm_GlobalTheory_CompanionTheory_MackeyFn_ip_ind
import Theorems.Thm_GlobalTheory_CompanionTheory_MackeyFn_mS_inv
import Theorems.Thm_GlobalTheory_CompanionTheory_MackeyFn_card_dc
import Theorems.Thm_GlobalTheory_CompanionTheory_MackeyFn_sum_dc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.MackeyFn
variable {Γ : Type} [Group Γ] [Fintype Γ]
namespace GlobalTheory.CompanionTheory.MackeyFn
theorem _root_.solution : ReciprocityTheory.Ty.Fin.St.MackeyIp := by
  classical
  intro Γ _ _ A B a b hA hB R _ g h1 h2
  have cardC : ∀ y, (Nat.card (A ⊓ cj y B : Subgroup Γ) : ℂ) ≠ 0 := fun y =>
    Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have cardA : (Nat.card A : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have cardB : (Nat.card B : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hvan : ∀ x, (∀ r, x ∉ dc A B (g r)) → mS A B a b x = 0 := by
    intro x hx
    rcases h2 x with ⟨r, β, hβ, α, hα, e⟩ | ⟨y, ⟨β, hβ, α, hα, rfl⟩, hy⟩
    · exact absurd ⟨β, hβ, α, hα, e⟩ (hx r)
    · rw [mS_inv hA hB y hβ hα]
      rw [ip_inter] at hy
      exact (mul_eq_zero.1 hy).resolve_left (inv_ne_zero (cardC y))
  have hdisj : ∀ x r r', x ∈ dc A B (g r) → x ∈ dc A B (g r') → r = r' := by
    rintro x r r' ⟨β, hβ, α, hα, rfl⟩ ⟨β', hβ', α', hα', e⟩
    refine h1 r r' ⟨β'⁻¹ * β, B.mul_mem (B.inv_mem hβ') hβ, α * α'⁻¹, A.mul_mem hα (A.inv_mem hα'), ?_⟩
    have : g r' = β'⁻¹ * (β' * g r' * α') * α'⁻¹ := by group
    rw [this, ← e]
    group
  have hsum : ∀ x, mS A B a b x = ∑ r, if x ∈ dc A B (g r) then mS A B a b x else 0 := by
    intro x
    by_cases hx : ∃ r, x ∈ dc A B (g r)
    · obtain ⟨r, hr⟩ := hx
      rw [Fintype.sum_eq_single r, if_pos hr]
      intro r' hne
      exact if_neg fun q => hne (hdisj x r r' hr q).symm
    · push_neg at hx
      rw [hvan x hx]
      simp
  rw [ip_ind, Finset.sum_congr rfl fun x _ => hsum x, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [sum_dc hA hB, ip_inter]
  have hc : (Nat.card (dc A B (g r)) : ℂ) * (Nat.card (A ⊓ cj (g r) B : Subgroup Γ) : ℂ) =
      (Nat.card A : ℂ) * (Nat.card B : ℂ) := by
    exact_mod_cast card_dc A B (g r)
  have := cardC (g r)
  field_simp
  linear_combination (mS A B a b (g r)) * hc
end GlobalTheory.CompanionTheory.MackeyFn
