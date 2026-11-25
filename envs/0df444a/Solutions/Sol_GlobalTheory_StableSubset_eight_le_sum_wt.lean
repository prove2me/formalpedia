-- Prove2me | solution 1 for GlobalTheory.StableSubset.eight_le_sum_wt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:47:00.973927+00:00
-- url     : https://prove2.me/submissions/56780fd6-875e-4693-9937-a06735359f1d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FactorialLeTwoMulCardPermWithFixedPointStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CardPermExistsStableSubsetLe
import Theorems.Thm_GlobalTheory_StableSubset_mem_iff_of_map_eq
import Theorems.Thm_GlobalTheory_StableSubset_map_eq_of_mem_iff
import Theorems.Thm_GlobalTheory_StableSubset_four_le_wt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Classical GlobalTheory.BadShare
open GlobalTheory GlobalTheory.StableSubset
open Finset Equiv
namespace GlobalTheory.StableSubset
theorem _root_.solution {N a : ℕ} (σ : Perm (Fin N)) (A : Finset (Fin N)) (hA : A.card = a)
    (h : A.map σ.toEmbedding = A) : 8 ≤ ∑ B ∈ powersetCard a (univ : Finset (Fin N)), wt B σ := by
  have hAm : A ∈ powersetCard a (univ : Finset (Fin N)) := by simp [hA]
  by_cases hb : (∃ i ∈ A, σ i = i) ∧ ∃ j ∉ A, σ j = j
  · obtain ⟨⟨i, hi, hσi⟩, ⟨j, hj, hσj⟩⟩ := hb
    set B := insert j (A.erase i) with hB
    have hjB : j ∈ B := Finset.mem_insert_self _ _
    have hne : A ≠ B := fun e => hj (e ▸ hjB)
    have hBc : B.card = a := by
      rw [hB, Finset.card_insert_of_notMem (fun hh => hj (Finset.mem_of_mem_erase hh)),
        Finset.card_erase_add_one hi, hA]
    have hBm : B ∈ powersetCard a (univ : Finset (Fin N)) := by simp [hBc]
    have hBs : B.map σ.toEmbedding = B := by
      apply map_eq_of_mem_iff
      intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hx
      · rw [hσj]; exact hjB
      · refine Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨?_, ?_⟩)
        · intro e
          exact (Finset.mem_erase.1 hx).1 (σ.injective (e.trans hσi.symm))
        · exact (mem_iff_of_map_eq σ A h x).2 (Finset.mem_erase.1 hx).2
    have hs : ({A, B} : Finset _) ⊆ powersetCard a (univ : Finset (Fin N)) := by
      intro C hC
      rcases Finset.mem_insert.1 hC with rfl | hC
      · exact hAm
      · rw [Finset.mem_singleton.1 hC]; exact hBm
    have := Finset.sum_le_sum_of_subset (f := fun B => wt B σ) hs
    rw [Finset.sum_pair hne] at this
    have h1 := four_le_wt A σ h
    have h2 := four_le_wt B σ hBs
    omega
  · have : wt A σ = 8 := by unfold wt; rw [if_pos h, if_neg hb]
    rw [← this]
    exact Finset.single_le_sum (f := fun B => wt B σ) (fun _ _ => Nat.zero_le _) hAm
end GlobalTheory.StableSubset
