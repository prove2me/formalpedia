-- Prove2me | solution 1 for KneserColouring.card_boundaryPairs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:49:55.466802+00:00
-- url     : https://prove2.me/submissions/f8f845c5-946a-4a0c-a8db-320d75a683cd

module
public import Mathlib
public import Definitions.Def_KneserLib_AltSets
public import Definitions.Def_KneserLib_TuckerRooms
public import Definitions.Def_KneserLib_TuckerParity
public import Theorems.Thm_KneserColouring_pref_update_of_le
public import Theorems.Thm_KneserColouring_range_succ_erase

set_option autoImplicit true
@[expose] public section
public section
open KneserColouring
open Finset
variable {n : ℕ}
namespace KneserColouring
theorem _root_.solution (lab : (Fin n → SignType) → ℤ) {k : ℕ} (hkn : k + 1 ≤ n) :
    (((doorPairs lab (k + 1)).filter (fun p => ¬ p.2 < k)).filter
      (fun p => ¬ p.1.2 ⟨k, by omega⟩ ≠ ⟨k, by omega⟩)).card =
    (univ.filter (fun r : Room n => IsRoom k r ∧ IsAlt 0 (labSet lab k r) ∧
      (labSet lab k r).card = k)).card := by
  set top : Fin n := ⟨k, by omega⟩ with htop
  have hlabs : ∀ (t : Fin n → SignType) (ρ : Equiv.Perm (Fin n)) (v : SignType), ρ top = top →
      ∀ i ∈ range k, rlab lab (Function.update t top v, ρ) i = rlab lab (t, ρ) i := by
    intro t ρ v hρ i hi
    rw [mem_range] at hi
    unfold rlab
    congr 1
    apply pref_update_of_le
    rw [hρ]
    change i + 1 ≤ k
    omega
  apply card_nbij' (fun p => (Function.update p.1.1 top 0, p.1.2))
    (fun r => ((Function.update r.1 top 1, r.2), k))
  · rintro ⟨⟨t, ρ⟩, j⟩ hp
    simp only [coe_filter, doorPairs, mem_filter, mem_product, mem_univ, true_and, mem_range,
      Set.mem_ofPred_eq, not_not] at hp ⊢
    obtain ⟨⟨⟨⟨hU, hj⟩, hD⟩, hjk⟩, hρ⟩ := hp
    have hjk' : j = k := by omega
    subst hjk'
    have hL : labSet lab j (Function.update t top 0, ρ) =
        ((range (j + 1)).erase j).image (rlab lab (t, ρ)) := by
      rw [range_succ_erase, labSet]
      exact image_congr (fun i hi => hlabs t ρ 0 hρ i hi)
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · intro c
      by_cases hc : c = top
      · subst hc
        simp [htop]
      · simp only [Function.update_of_ne hc]
        rw [hU.1.1 c]
        have : c.val ≠ j := fun h => hc (Fin.ext h)
        omega
    · intro c hc
      by_cases hct : c = top
      · rw [hct]
        exact hρ
      · exact hU.1.2 c (by have : c.val ≠ j := fun h => hct (Fin.ext h); omega)
    · rw [hL]
      exact hD.2
    · rw [hL]
      have := hD.1
      rw [card_range] at this
      omega
  · rintro ⟨t, ρ⟩ hr
    simp only [coe_filter, doorPairs, mem_filter, mem_product, mem_univ, true_and, mem_range,
      Set.mem_ofPred_eq, not_not] at hr ⊢
    obtain ⟨hR, hA, hc⟩ := hr
    have hρ : ρ top = top := hR.2 top (by simp [htop])
    have hL : labSet lab k (t, ρ) =
        ((range (k + 1)).erase k).image (rlab lab (Function.update t top 1, ρ)) := by
      rw [range_succ_erase, labSet]
      exact image_congr (fun i hi => (hlabs t ρ 1 hρ i hi).symm)
    refine ⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, by omega⟩, ?_, ?_⟩, by omega⟩, hρ⟩
    · intro c
      by_cases hct : c = top
      · subst hct
        simp [htop]
      · simp only [Function.update_of_ne hct]
        rw [hR.1 c]
        have : c.val ≠ k := fun h => hct (Fin.ext h)
        omega
    · intro c hc
      exact hR.2 c (by omega)
    · intro c hc
      have hct : c = top := Fin.ext (by simp [htop]; omega)
      subst hct
      simp
    · rw [← hL, card_range, hc]
    · rw [← hL]
      exact hA
  · rintro ⟨⟨t, ρ⟩, j⟩ hp
    simp only [coe_filter, doorPairs, mem_filter, mem_product, mem_univ, true_and, mem_range,
      Set.mem_ofPred_eq, not_not] at hp
    obtain ⟨⟨⟨⟨hU, hj⟩, hD⟩, hjk⟩, hρ⟩ := hp
    have hjk' : j = k := by omega
    subst hjk'
    have ht : t top = 1 := hU.2 top (by simp [htop])
    simp only [Function.update_idem, Prod.mk.injEq, and_true]
    rw [← ht, Function.update_eq_self]
  · rintro ⟨t, ρ⟩ hr
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hr
    have ht : t top = 0 := by
      by_contra h
      have := (hr.1.1 top).1 h
      simp [htop] at this
    simp only [Function.update_idem, Prod.mk.injEq, and_true]
    rw [← ht, Function.update_eq_self]
end KneserColouring
