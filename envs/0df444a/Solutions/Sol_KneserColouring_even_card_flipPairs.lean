-- Prove2me | solution 1 for KneserColouring.even_card_flipPairs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:50:15.173283+00:00
-- url     : https://prove2.me/submissions/c15bac69-68d0-49e6-b21d-2b3bc97463ab

module
public import Mathlib
public import Definitions.Def_KneserLib_AltSets
public import Definitions.Def_KneserLib_TuckerRooms
public import Definitions.Def_KneserLib_TuckerParity
public import Theorems.Thm_KneserColouring_signType_neg_ne_zero
public import Theorems.Thm_KneserColouring_signType_neg_ne_self
public import Theorems.Thm_KneserColouring_pref_update_of_le
public import Theorems.Thm_KneserColouring_range_succ_erase
public import Theorems.Thm_KneserColouring_even_card_of_involution


set_option autoImplicit true
@[expose] public section
public section
open KneserColouring
open Finset
variable {n : ℕ}
namespace KneserColouring
theorem _root_.solution (lab : (Fin n → SignType) → ℤ) {k : ℕ} (hkn : k + 1 ≤ n) :
    Even (((doorPairs lab (k + 1)).filter (fun p => ¬ p.2 < k)).filter
      (fun p => p.1.2 ⟨k, by omega⟩ ≠ ⟨k, by omega⟩)).card := by
  set top : Fin n := ⟨k, by omega⟩ with htop
  apply even_card_of_involution _ (fun p => ((Function.update p.1.1 (p.1.2.symm top)
    (-p.1.1 (p.1.2.symm top)), p.1.2), p.2))
  · rintro ⟨⟨t, ρ⟩, j⟩ hp
    simp only [doorPairs, mem_filter, mem_product, mem_univ, true_and, mem_range] at hp ⊢
    obtain ⟨⟨⟨⟨hU, hj⟩, hD⟩, hjk⟩, hρ⟩ := hp
    set c0 := ρ.symm top with hc0
    have hρc0 : ρ c0 = top := by simp [hc0]
    have hc0top : c0 ≠ top := by
      intro h
      apply hρ
      have h2 := hρc0
      rw [h] at h2
      exact h2
    have hc0lt : c0.val < k := by
      have : c0.val < k + 1 := by
        by_contra h'
        have h2 := hU.1.2 c0 (by omega)
        rw [hρc0] at h2
        exact hc0top h2.symm
      have : c0.val ≠ k := fun h => hc0top (Fin.ext h)
      omega
    have hjk' : j = k := by omega
    subst hjk'
    have hlab : ∀ i ∈ (range (j + 1)).erase j,
        rlab lab (Function.update t c0 (-t c0), ρ) i = rlab lab (t, ρ) i := by
      intro i hi
      rw [range_succ_erase, mem_range] at hi
      unfold rlab
      congr 1
      apply pref_update_of_le
      simp only [hρc0, htop]
      omega
    refine ⟨⟨⟨⟨?_, hj⟩, ?_⟩, hjk⟩, hρ⟩
    · refine ⟨⟨?_, hU.1.2⟩, ?_⟩
      · intro c
        by_cases hc : c = c0
        · subst hc
          simp only [Function.update_self]
          rw [signType_neg_ne_zero]
          exact hU.1.1 c0
        · simp only [Function.update_of_ne hc]
          exact hU.1.1 c
      · intro c hc
        have hct : c = top := Fin.ext (by simp [htop]; omega)
        have : c ≠ c0 := fun h => hc0top (h ▸ hct)
        simp only [Function.update_of_ne this]
        exact hU.2 c hc
    · unfold door at hD ⊢
      rw [image_congr (fun i hi => hlab i hi)]
      exact hD
  · rintro ⟨⟨t, ρ⟩, j⟩ hp heq
    simp only [doorPairs, mem_filter, mem_product, mem_univ, true_and, mem_range] at hp
    obtain ⟨⟨⟨⟨hU, hj⟩, hD⟩, hjk⟩, hρ⟩ := hp
    simp only [Prod.mk.injEq, and_true] at heq
    set c0 := ρ.symm top with hc0
    have hρc0 : ρ c0 = top := by simp [hc0]
    have hc0lt : c0.val < k + 1 := by
      by_contra h'
      have h2 := hU.1.2 c0 (by omega)
      rw [hρc0] at h2
      apply hρ
      conv_lhs => rw [h2]
      exact hρc0
    have hne : t c0 ≠ 0 := (hU.1.1 c0).2 hc0lt
    have h2 := congrFun heq c0
    simp only [Function.update_self] at h2
    exact signType_neg_ne_self hne h2
  · rintro ⟨⟨t, ρ⟩, j⟩ _
    simp [Function.update_idem]
end KneserColouring
