-- Prove2me | solution 1 for KneserColouring.even_card_swapPairs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:49:52.550506+00:00
-- url     : https://prove2.me/submissions/a77f103f-f807-43de-ab95-e610c879ea55

module
public import Mathlib
public import Definitions.Def_KneserLib_AltSets
public import Definitions.Def_KneserLib_TuckerRooms
public import Definitions.Def_KneserLib_TuckerParity
public import Theorems.Thm_KneserColouring_adjSwap_adjSwap
public import Theorems.Thm_KneserColouring_adjSwap_val
public import Theorems.Thm_KneserColouring_even_card_of_involution
public import Theorems.Thm_KneserColouring_pref_congr


set_option autoImplicit true
@[expose] public section
public section
open KneserColouring
open Finset
variable {n : ℕ}
namespace KneserColouring
theorem _root_.solution (lab : (Fin n → SignType) → ℤ) {k : ℕ} (hkn : k + 1 ≤ n) :
    Even ((doorPairs lab (k + 1)).filter (fun p => p.2 < k)).card := by
  apply even_card_of_involution _ (fun p => ((p.1.1, p.1.2.trans (adjSwap n p.2)), p.2))
  · rintro ⟨⟨t, ρ⟩, j⟩ hp
    simp only [doorPairs, mem_filter, mem_product, mem_univ, true_and, mem_range] at hp ⊢
    obtain ⟨⟨⟨hU, hj⟩, hD⟩, hjk⟩ := hp
    have hj1 : j + 1 < n := by omega
    have hlab : ∀ i ∈ (range (k + 1)).erase j,
        rlab lab (t, ρ.trans (adjSwap n j)) i = rlab lab (t, ρ) i := by
      intro i hi
      have hij : i ≠ j := (mem_erase.1 hi).1
      unfold rlab
      congr 1
      apply pref_congr
      · intro c
        simp only [Equiv.trans_apply]
        rw [adjSwap_val hj1]
        split_ifs <;> omega
      · intro c _
        rfl
    refine ⟨⟨⟨?_, hj⟩, ?_⟩, hjk⟩
    · refine ⟨⟨hU.1.1, ?_⟩, hU.2⟩
      intro c hc
      simp only [Equiv.trans_apply]
      rw [hU.1.2 c hc]
      apply Fin.ext
      rw [adjSwap_val hj1]
      split_ifs <;> omega
    · unfold door at hD ⊢
      rw [image_congr (fun i hi => hlab i hi)]
      exact hD
  · rintro ⟨⟨t, ρ⟩, j⟩ hp heq
    simp only [doorPairs, mem_filter, mem_product, mem_univ, true_and, mem_range] at hp
    have hj1 : j + 1 < n := by omega
    simp only [Prod.mk.injEq, and_true, true_and] at heq
    have h2 := congrArg (fun σ : Equiv.Perm (Fin n) => (σ (ρ.symm ⟨j, by omega⟩)).val) heq
    simp only [Equiv.trans_apply, Equiv.apply_symm_apply] at h2
    rw [adjSwap_val hj1] at h2
    simp at h2
  · rintro ⟨⟨t, ρ⟩, j⟩ _
    simp only [Prod.mk.injEq, and_true, true_and]
    ext c
    simp [Equiv.trans_apply, adjSwap_adjSwap]
end KneserColouring
