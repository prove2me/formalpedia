-- Prove2me | solution 1 for GlobalTheory.BadShare.factorial_le_two_mul_card_perm_fixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:29:42.259878+00:00
-- url     : https://prove2.me/submissions/09721998-f245-4d1b-9834-cab8e48905a8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FactorialLeTwoMulCardPermWithFixedPoint
import Theorems.Thm_GlobalTheory_BadShare_two_mul_numDerangements_succ_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Classical GlobalTheory.BadShare
open GlobalTheory GlobalTheory.BadShare
namespace GlobalTheory.BadShare
theorem _root_.solution :
    ∀ (α : Type) [Fintype α] [DecidableEq α], Nonempty α →
      (Fintype.card α).factorial ≤
        2 * (Finset.univ.filter fun σ : Equiv.Perm α => ∃ i, σ i = i).card := by
  intro α _ _ hne
  have hsum := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Equiv.Perm α)))
    (fun σ : Equiv.Perm α => ∃ i, σ i = i)
  rw [Finset.card_univ, Fintype.card_perm] at hsum
  have hd : (Finset.univ.filter fun σ : Equiv.Perm α => ¬ ∃ i, σ i = i).card
      = numDerangements (Fintype.card α) := by
    rw [← card_derangements_eq_numDerangements α, ← Fintype.card_subtype]
    refine Fintype.card_congr (Equiv.subtypeEquivRight fun σ => ?_)
    simp [derangements]
  obtain ⟨n, hn⟩ : ∃ n, Fintype.card α = n + 1 :=
    Nat.exists_eq_succ_of_ne_zero Fintype.card_ne_zero
  have h := two_mul_numDerangements_succ_le n
  rw [← hn] at h
  omega
end GlobalTheory.BadShare
