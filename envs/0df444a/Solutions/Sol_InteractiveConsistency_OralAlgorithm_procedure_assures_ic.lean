-- Prove2me | solution 1 for InteractiveConsistency.OralAlgorithm.procedure_assures_ic
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T05:19:18.712979+00:00
-- url     : https://prove2.me/submissions/7cea63e2-96c2-43b3-810e-c12b8cd70da0

import Mathlib
import Definitions.Def_InteractiveConsistency_OralAlgorithm_Scenario
import Definitions.Def_InteractiveConsistency_OralAlgorithm_Procedure



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

theorem strip_core {α V : Type*} [DecidableEq α] (P N : Finset α) (m : ℕ)
    (hNP : N ⊆ P) (σ : List α → V) (hσ : ConsistentUpTo P N (m + 1) σ) (q : α) (hq : q ∈ N) :
    ∀ (u : List α) (p : α), p ∈ P → IsStringOver N u → u.length ≤ m →
      σ (p :: (u ++ [q])) = σ [q] := by
  intro u
  induction u with
  | nil =>
    intro p hp _ _
    have := hσ q hq p hp [] (by simp [IsStringOver]) (by simp)
    simpa using this
  | cons x u' ih =>
    intro p hp hu hlen
    have hx : x ∈ N := hu x (by simp)
    have hu' : IsStringOver N u' := fun y hy => hu y (by simp [hy])
    have hw : IsStringOver P (u' ++ [q]) := by
      intro y hy
      rcases List.mem_append.1 hy with h | h
      · exact hNP (hu' y h)
      · simp at h; exact h ▸ hNP hq
    have h1 := hσ x hx p hp (u' ++ [q]) hw (by simp at hlen ⊢; omega)
    have h2 := ih x (hNP hx) hu' (by simp at hlen; omega)
    simp only [List.cons_append] at h1 ⊢
    rw [h1]; exact h2

theorem record_stepone {α V : Type*} [DecidableEq α] (m : ℕ) (P : Finset α) (τ : List α → V)
    (q : α) (h : StepOne m P τ q) : record m P τ q = some (τ [q]) := by
  cases m <;> simp [record, h]

theorem record_of_nonfaulty_core {α V : Type*} [DecidableEq α] (P N : Finset α) (m : ℕ)
    (hn : 3 * m + 1 ≤ P.card) (hNP : N ⊆ P) (hN : P.card ≤ N.card + m)
    (σ : List α → V) (hσ : ConsistentUpTo P N (m + 1) σ)
    (p q : α) (hp : p ∈ N) (hq : q ∈ N) :
    StepOne m P (fun w => σ (p :: w)) q ∧
      record m P (fun w => σ (p :: w)) q = some (σ [q]) := by
  have hS : StepOne m P (fun w => σ (p :: w)) q := by
    refine ⟨N, hNP, by omega, σ [q], ?_⟩
    intro w hw hlen
    exact strip_core P N m hNP σ hσ q hq w p (hNP hp) hw hlen
  refine ⟨hS, ?_⟩
  rw [record_stepone _ _ _ _ hS]
  have := strip_core P N m hNP σ hσ q hq [] p (hNP hp) (by simp [IsStringOver]) (by simp)
  simpa using this

open Classical in
/-- number of entries of the sub-vector with value `x` -/
noncomputable def cntE {α V : Type*} [DecidableEq α] (m' : ℕ) (P : Finset α) (τ : List α → V)
    (q : α) (x : Option V) : ℕ :=
  ((P.erase q).filter (fun q' => record m' (P.erase q) (fun w => τ (w ++ [q])) q' = x)).card

open Classical in
theorem cnt_uniq {α V : Type*} [DecidableEq α] (m' : ℕ) (P : Finset α) (τ : List α → V)
    (q : α) (hq : q ∈ P) (x y : Option V)
    (hx : (P.card + (m' + 1)) / 2 ≤ cntE m' P τ q x)
    (hy : (P.card + (m' + 1)) / 2 ≤ cntE m' P τ q y) : x = y := by
  by_contra hxy
  unfold cntE at hx hy
  have hd : Disjoint ((P.erase q).filter (fun q' => record m' (P.erase q) (fun w => τ (w ++ [q])) q' = x))
      ((P.erase q).filter (fun q' => record m' (P.erase q) (fun w => τ (w ++ [q])) q' = y)) := by
    rw [Finset.disjoint_filter]
    intro a _ h1 h2
    exact hxy (h1.symm.trans h2)
  have hu := Finset.card_le_card (Finset.union_subset (Finset.filter_subset
      (fun q' => record m' (P.erase q) (fun w => τ (w ++ [q])) q' = x) (P.erase q))
      (Finset.filter_subset (fun q' => record m' (P.erase q) (fun w => τ (w ++ [q])) q' = y) (P.erase q)))
  rw [Finset.card_union_of_disjoint hd] at hu
  have hc : (P.erase q).card + 1 = P.card := by
    rw [Finset.card_erase_of_mem hq]
    have : 0 < P.card := Finset.card_pos.2 ⟨q, hq⟩
    omega
  omega

open Classical in
theorem record_succ_prop {α V : Type*} [DecidableEq α] (m' : ℕ) (P : Finset α) (τ : List α → V)
    (q : α) (hq : q ∈ P) :
    (P.card + (m' + 1)) / 2 ≤ cntE m' P τ q (record (m' + 1) P τ q) ∨
      (record (m' + 1) P τ q = none ∧ ∀ x, cntE m' P τ q x < (P.card + (m' + 1)) / 2) := by
  by_cases hs : StepOne (m' + 1) P τ q
  · left
    rw [record_stepone _ _ _ _ hs]
    obtain ⟨Q, hQP, hQc, v, hv⟩ := hs
    have hτ : τ [q] = v := by simpa using hv [] (by simp [IsStringOver]) (by simp)
    rw [hτ]
    obtain ⟨h1, h2, h3, h4⟩ := hat_quorum_core P m' (fun l => τ l.tail) q q hq Q hQP hQc v
      (by intro w hw hl; simpa using hv w hw hl)
    refine le_trans h2 ?_
    unfold cntE
    apply Finset.card_le_card
    intro q' hq'
    refine Finset.mem_filter.2 ⟨h1 hq', ?_⟩
    have hsub : StepOne m' (P.erase q) (fun w => τ (w ++ [q])) q' := by
      refine ⟨Q.erase q, h1, h3, v, ?_⟩
      intro w hw hl
      simpa using h4 q' hq' w hw hl
    rw [record_stepone _ _ _ _ hsub]
    have := h4 q' hq' [] (by simp [IsStringOver]) (by simp)
    simpa using this
  · have hrec : record (m' + 1) P τ q =
        if h : ∃ x : Option V, (P.card + (m' + 1)) / 2 ≤ cntE m' P τ q x
        then Classical.choose h else none := by
      rw [record]; simp only [hs, if_false]; rfl
    by_cases h : ∃ x : Option V, (P.card + (m' + 1)) / 2 ≤ cntE m' P τ q x
    · left
      rw [hrec, dif_pos h]
      exact Classical.choose_spec h
    · right
      refine ⟨by rw [hrec, dif_neg h], ?_⟩
      intro x
      by_contra hx
      exact h ⟨x, not_lt.1 hx⟩

open Classical in
theorem agree_core {α V : Type*} [DecidableEq α] (m : ℕ) :
    ∀ (P N : Finset α) (σ : List α → V), 3 * m + 1 ≤ P.card → N ⊆ P → P.card ≤ N.card + m →
      ConsistentUpTo P N (m + 1) σ →
      ∀ p ∈ N, ∀ p' ∈ N, ∀ r ∈ P,
        record m P (fun w => σ (p :: w)) r = record m P (fun w => σ (p' :: w)) r := by
  induction m with
  | zero =>
    intro P N σ hn hNP hN hσ p hp p' hp' r hr
    have hPN : N = P := Finset.eq_of_subset_of_card_le hNP (by omega)
    have hrN : r ∈ N := hPN ▸ hr
    rw [(record_of_nonfaulty_core P N 0 hn hNP hN σ hσ p r hp hrN).2,
      (record_of_nonfaulty_core P N 0 hn hNP hN σ hσ p' r hp' hrN).2]
  | succ m' ih =>
    intro P N σ hn hNP hN hσ p hp p' hp' r hr
    by_cases hrN : r ∈ N
    · rw [(record_of_nonfaulty_core P N _ hn hNP hN σ hσ p r hp hrN).2,
        (record_of_nonfaulty_core P N _ hn hNP hN σ hσ p' r hp' hrN).2]
    · obtain ⟨hs1, hs2, hs3⟩ := subscenario_core P N m' hNP hN σ hσ r hr hrN
      have hcard : (P.erase r).card + 1 = P.card := by
        rw [Finset.card_erase_of_mem hr]
        have : 0 < P.card := Finset.card_pos.2 ⟨r, hr⟩
        omega
      have hvec : ∀ q' ∈ P.erase r,
          record m' (P.erase r) (fun w => (fun w => σ (p :: w)) (w ++ [r])) q' =
          record m' (P.erase r) (fun w => (fun w => σ (p' :: w)) (w ++ [r])) q' := by
        intro q' hq'
        exact ih (P.erase r) N (fun w => σ (w ++ [r])) (by omega) hs1 hs2 hs3 p hp p' hp' q' hq'
      have hcnt : ∀ x, cntE m' P (fun w => σ (p :: w)) r x = cntE m' P (fun w => σ (p' :: w)) r x := by
        intro x
        unfold cntE
        congr 1
        apply Finset.filter_congr
        intro q' hq'
        rw [hvec q' hq']
      rcases record_succ_prop m' P (fun w => σ (p :: w)) r hr with h1 | ⟨h1, h1'⟩ <;>
      rcases record_succ_prop m' P (fun w => σ (p' :: w)) r hr with h2 | ⟨h2, h2'⟩
      · exact cnt_uniq m' P (fun w => σ (p :: w)) r hr _ _ h1 (by rw [hcnt]; exact h2)
      · exfalso
        have := h2' (record (m' + 1) P (fun w => σ (p :: w)) r)
        rw [← hcnt] at this
        omega
      · exfalso
        have := h1' (record (m' + 1) P (fun w => σ (p' :: w)) r)
        rw [hcnt] at this
        omega
      · rw [h1, h2]

theorem procedure_core {α V : Type*} [DecidableEq α] (P : Finset α) (m : ℕ)
    (hn : 3 * m + 1 ≤ P.card) :
    AssuresICLevel (V := V) P m (fun _ => record m P) := by
  intro N hNP hN σ hσ
  refine ⟨?_, ?_⟩
  · intro p hp q hq
    exact (record_of_nonfaulty_core P N m hn hNP hN σ hσ p q hp hq).2
  · intro p hp p' hp' r hr
    exact agree_core m P N σ hn hNP hN hσ p hp p' hp' r hr

end InteractiveConsistency.OralAlgorithm

open InteractiveConsistency.OralAlgorithm


theorem solution {α V : Type*} [DecidableEq α] (P : Finset α) (m : ℕ)
    (hn : 3 * m + 1 ≤ P.card) :
    AssuresICLevel (V := V) P m (fun _ => record m P) := by
  exact procedure_core P m hn
