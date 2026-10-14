-- Prove2me | solution 1 for InteractiveConsistency.OralAlgorithm.subscenario_consistent
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T05:17:10.596009+00:00
-- url     : https://prove2.me/submissions/d1a2af9e-a46d-4a98-8fad-b15d1ab5429a

import Mathlib
import Definitions.Def_InteractiveConsistency_OralAlgorithm_Scenario



namespace InteractiveConsistency.OralAlgorithm

theorem subscenario_core {α V : Type*} [DecidableEq α] (P N : Finset α) (m' : ℕ)
    (hNP : N ⊆ P) (hN : P.card ≤ N.card + (m' + 1))
    (σ : List α → V) (hσ : ConsistentUpTo P N (m' + 2) σ)
    (q : α) (hqP : q ∈ P) (hqN : q ∉ N) :
    N ⊆ P.erase q ∧ (P.erase q).card ≤ N.card + m' ∧
      ConsistentUpTo (P.erase q) N (m' + 1) (fun w => σ (w ++ [q])) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    exact Finset.mem_erase.2 ⟨fun h => hqN (h ▸ hx), hNP hx⟩
  · rw [Finset.card_erase_of_mem hqP]; omega
  · intro q0 hq0 p hp w hw hlen
    have hpP : p ∈ P := Finset.mem_of_mem_erase hp
    have hw' : IsStringOver P (w ++ [q]) := by
      intro x hx
      rcases List.mem_append.1 hx with h | h
      · exact Finset.mem_of_mem_erase (hw x h)
      · simp at h; exact h ▸ hqP
    have := hσ q0 hq0 p hpP (w ++ [q]) hw' (by simp; omega)
    simpa using this

theorem hat_quorum_core {α V : Type*} [DecidableEq α] (P : Finset α) (m' : ℕ)
    (σ : List α → V) (p' q : α) (hqP : q ∈ P)
    (Q : Finset α) (hQP : Q ⊆ P) (hQcard : P.card + (m' + 1) < 2 * Q.card) (v : V)
    (hv : ∀ w : List α, IsStringOver Q w → w.length ≤ m' + 1 → σ (p' :: (w ++ [q])) = v) :
    Q.erase q ⊆ P.erase q ∧
      (P.card + (m' + 1)) / 2 ≤ (Q.erase q).card ∧
      (P.erase q).card + m' < 2 * (Q.erase q).card ∧
      ∀ q' ∈ Q.erase q, ∀ w : List α, IsStringOver (Q.erase q) w → w.length ≤ m' →
        σ (p' :: ((w ++ [q']) ++ [q])) = v := by
  have hc : Q.card ≤ (Q.erase q).card + 1 := by
    have := Finset.pred_card_le_card_erase (s := Q) (a := q)
    omega
  have hPc : (P.erase q).card + 1 = P.card := by
    rw [Finset.card_erase_of_mem hqP]
    have : 0 < P.card := Finset.card_pos.2 ⟨q, hqP⟩
    omega
  refine ⟨Finset.erase_subset_erase q hQP, ?_, ?_, ?_⟩
  · omega
  · omega
  · intro q' hq' w hw hlen
    have hq'Q : q' ∈ Q := Finset.mem_of_mem_erase hq'
    have := hv (w ++ [q']) (by
      intro x hx
      rcases List.mem_append.1 hx with h | h
      · exact Finset.mem_of_mem_erase (hw x h)
      · simp at h; exact h ▸ hq'Q) (by simp; omega)
    exact this

theorem step_one_agree_core {α V : Type*} [DecidableEq α] (P N : Finset α) (m : ℕ)
    (hNP : N ⊆ P) (hN : P.card ≤ N.card + m)
    (σ : List α → V) (hσ : ConsistentUpTo P N (m + 1) σ)
    (p p' q : α) (hp : p ∈ N) (hp' : p' ∈ N) (hq : q ∈ P)
    (Q₁ Q₂ : Finset α) (hQ₁ : Q₁ ⊆ P) (hQ₂ : Q₂ ⊆ P)
    (hQ₁card : P.card + m < 2 * Q₁.card) (hQ₂card : P.card + m < 2 * Q₂.card)
    (v v' : V)
    (hv : ∀ w : List α, IsStringOver Q₁ w → w.length ≤ m → σ (p :: (w ++ [q])) = v)
    (hv' : ∀ w : List α, IsStringOver Q₂ w → w.length ≤ m → σ (p' :: (w ++ [q])) = v') :
    v = v' := by
  have hI : (Q₁ ∩ Q₂ ∩ N).Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    have hsub : Q₁ ∩ Q₂ ⊆ P \ N := by
      intro x hx
      have hxP : x ∈ P := hQ₁ (Finset.mem_inter.1 hx).1
      refine Finset.mem_sdiff.2 ⟨hxP, fun hxN => ?_⟩
      have : x ∈ Q₁ ∩ Q₂ ∩ N := Finset.mem_inter.2 ⟨hx, hxN⟩
      rw [hne] at this; simp at this
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_sdiff_add_card_eq_card hNP
    have h3 := Finset.card_union_add_card_inter Q₁ Q₂
    have h4 : (Q₁ ∪ Q₂).card ≤ P.card := Finset.card_le_card (Finset.union_subset hQ₁ hQ₂)
    omega
  obtain ⟨x, hx⟩ := hI
  have hxQ1 : x ∈ Q₁ := (Finset.mem_inter.1 (Finset.mem_inter.1 hx).1).1
  have hxQ2 : x ∈ Q₂ := (Finset.mem_inter.1 (Finset.mem_inter.1 hx).1).2
  have hxN : x ∈ N := (Finset.mem_inter.1 hx).2
  have hpP : p ∈ P := hNP hp
  have hp'P : p' ∈ P := hNP hp'
  rcases Nat.eq_zero_or_pos m with h0 | hm
  · subst h0
    have hqN : q ∈ N := by
      by_contra hqN
      have : P ⊆ N := by
        have := Finset.eq_of_subset_of_card_le hNP (by omega)
        rw [this]
      exact hqN (this hq)
    have e1 := hv [] (by simp [IsStringOver]) (by simp)
    have e2 := hv' [] (by simp [IsStringOver]) (by simp)
    have c1 := hσ q hqN p hpP [] (by simp [IsStringOver]) (by simp)
    have c2 := hσ q hqN p' hp'P [] (by simp [IsStringOver]) (by simp)
    simp at e1 e2 c1 c2
    rw [← e1, ← e2, c1, c2]
  · have e1 := hv [x] (by simp [IsStringOver]; exact hxQ1) (by simp; omega)
    have e2 := hv' [x] (by simp [IsStringOver]; exact hxQ2) (by simp; omega)
    have hqL : IsStringOver P [q] := by simp [IsStringOver]; exact hq
    have c1 := hσ x hxN p hpP [q] hqL (by simp; omega)
    have c2 := hσ x hxN p' hp'P [q] hqL (by simp; omega)
    simp at e1 e2 c1 c2
    rw [← e1, ← e2, c1, c2]

end InteractiveConsistency.OralAlgorithm

open InteractiveConsistency.OralAlgorithm


theorem solution {α V : Type*} [DecidableEq α] (P N : Finset α) (m' : ℕ)
    (hNP : N ⊆ P) (hN : P.card ≤ N.card + (m' + 1))
    (σ : List α → V) (hσ : ConsistentUpTo P N (m' + 2) σ)
    (q : α) (hqP : q ∈ P) (hqN : q ∉ N) :
    N ⊆ P.erase q ∧ (P.erase q).card ≤ N.card + m' ∧
      ConsistentUpTo (P.erase q) N (m' + 1) (fun w => σ (w ++ [q])) := by
  exact subscenario_core P N m' hNP hN σ hσ q hqP hqN
