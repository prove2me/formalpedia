-- Prove2me | solution 2 for InteractiveConsistency.OralAlgorithm.procedure_assures_ic
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T10:24:16.437886+00:00
-- url     : https://prove2.me/submissions/a06731a5-9a45-4f5c-aff2-b8d47f2a2b72

import Mathlib
import Definitions.Def_InteractiveConsistency_OralAlgorithm_Scenario
import Definitions.Def_InteractiveConsistency_OralAlgorithm_Procedure
import Theorems.Thm_InteractiveConsistency_OralAlgorithm_hat_quorum_step_one
import Theorems.Thm_InteractiveConsistency_OralAlgorithm_record_of_nonfaulty
import Theorems.Thm_InteractiveConsistency_OralAlgorithm_subscenario_consistent

-- carved verbatim out of submission 7cea63e2-96c2-43b3-810e-c12b8cd70da0, lines 282-286

section
open InteractiveConsistency
open InteractiveConsistency.OralAlgorithm

theorem record_stepone {α V : Type*} [DecidableEq α] (m : ℕ) (P : Finset α) (τ : List α → V)
    (q : α) (h : StepOne m P τ q) : record m P τ q = some (τ [q]) := by
  cases m <;> simp [record, h]

open Classical in
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
    obtain ⟨h1, h2, h3, h4⟩ := InteractiveConsistency.OralAlgorithm.hat_quorum_step_one P m' (fun l => τ l.tail) q q hq Q hQP hQc v
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
    rw [(InteractiveConsistency.OralAlgorithm.record_of_nonfaulty P N 0 hn hNP hN σ hσ p r hp hrN).2,
      (InteractiveConsistency.OralAlgorithm.record_of_nonfaulty P N 0 hn hNP hN σ hσ p' r hp' hrN).2]
  | succ m' ih =>
    intro P N σ hn hNP hN hσ p hp p' hp' r hr
    by_cases hrN : r ∈ N
    · rw [(InteractiveConsistency.OralAlgorithm.record_of_nonfaulty P N _ hn hNP hN σ hσ p r hp hrN).2,
        (InteractiveConsistency.OralAlgorithm.record_of_nonfaulty P N _ hn hNP hN σ hσ p' r hp' hrN).2]
    · obtain ⟨hs1, hs2, hs3⟩ := InteractiveConsistency.OralAlgorithm.subscenario_consistent P N m' hNP hN σ hσ r hr hrN
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
    exact (InteractiveConsistency.OralAlgorithm.record_of_nonfaulty P N m hn hNP hN σ hσ p q hp hq).2
  · intro p hp p' hp' r hr
    exact agree_core m P N σ hn hNP hN hσ p hp p' hp' r hr

end

section
open InteractiveConsistency.OralAlgorithm

theorem solution {α V : Type*} [DecidableEq α] (P : Finset α) (m : ℕ)
    (hn : 3 * m + 1 ≤ P.card) :
    AssuresICLevel (V := V) P m (fun _ => record m P) := by
  exact procedure_core P m hn

end
