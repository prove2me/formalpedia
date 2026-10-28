-- Prove2me | solution 1 for NQueensComp.NPC.lemma_30
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T00:48:54.472655+00:00
-- url     : https://prove2.me/submissions/f1c03cf2-c6c7-4626-a423-06bb79a58e1c

import Mathlib
import Definitions.Def_NQueensComp_NPC_Reductions

open NQueensComp.NPC

theorem dBlue_le (k : ℕ) : dBlue k ≤ 6 := by
  match k with
  | 0 => simp [dBlue]
  | 1 => simp [dBlue]
  | k + 2 => simp [dBlue]

theorem dRed_le (k : ℕ) : dRed k ≤ 6 := by
  match k with
  | 0 => simp [dRed]
  | 1 => simp [dRed]
  | k + 2 => simp [dRed]

/-- The arithmetic core: columns of the form `21x + a` with `a ≤ 6` and rows in `{0, 7, 14}`
determine the queen from either diagonal. -/
theorem key (C R : Finset ℕ) (hC : ∀ c ∈ C, ∃ x a, c = 21 * x + a ∧ a ≤ 6)
    (hR : ∀ r ∈ R, r = 0 ∨ r = 7 ∨ r = 14) :
    (∀ p ∈ C ×ˢ R, ∀ p' ∈ C ×ˢ R, diffDiag p = diffDiag p' → p = p') ∧
    (∀ p ∈ C ×ˢ R, ∀ p' ∈ C ×ˢ R, sumDiag p = sumDiag p' → p = p') := by
  constructor
  · intro p hp p' hp' h
    rw [Finset.mem_product] at hp hp'
    obtain ⟨x, a, hc, ha⟩ := hC p.1 hp.1
    obtain ⟨x', a', hc', ha'⟩ := hC p'.1 hp'.1
    have hr := hR p.2 hp.2
    have hr' := hR p'.2 hp'.2
    simp only [diffDiag] at h
    rw [Prod.ext_iff]
    omega
  · intro p hp p' hp' h
    rw [Finset.mem_product] at hp hp'
    obtain ⟨x, a, hc, ha⟩ := hC p.1 hp.1
    obtain ⟨x', a', hc', ha'⟩ := hC p'.1 hp'.1
    have hr := hR p.2 hp.2
    have hr' := hR p'.2 hp'.2
    simp only [sumDiag] at h
    rw [Prod.ext_iff]
    omega

theorem solution (cs : Inst6) (hcs : Inst6Valid cs) (j : ℕ) (hj : j < cs.length) :
    ∀ G ∈ [G1 cs j, G2 cs j, G3 cs j],
      (∀ p ∈ G.C ×ˢ G.R, ∀ p' ∈ G.C ×ˢ G.R, diffDiag p = diffDiag p' → p = p') ∧
      (∀ p ∈ G.C ×ˢ G.R, ∀ p' ∈ G.C ×ˢ G.R, sumDiag p = sumDiag p' → p = p') := by
  have hb : ∀ v, ∃ x a, colBlue cs j v = 21 * x + a ∧ a ≤ 6 :=
    fun v => ⟨varIdx cs v, dBlue (occRank cs v j), rfl, dBlue_le _⟩
  have hr : ∀ v, ∃ x a, colRed cs j v = 21 * x + a ∧ a ≤ 6 :=
    fun v => ⟨varIdx cs v, dRed (occRank cs v j), rfl, dRed_le _⟩
  intro G hG
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hG
  rcases hG with rfl | rfl | rfl
  · apply key
    · intro c hc
      simp only [G1, Finset.mem_insert, Finset.mem_singleton] at hc
      rcases hc with rfl | rfl | rfl <;> exact hb _
    · intro r hr
      simp only [G1, Finset.mem_insert, Finset.mem_singleton] at hr
      exact hr
  · apply key
    · intro c hc
      simp only [G2, Finset.mem_insert, Finset.mem_singleton] at hc
      rcases hc with rfl | rfl <;> exact hr _
    · intro r hr
      simp only [G2, Finset.mem_insert, Finset.mem_singleton] at hr
      omega
  · apply key
    · intro c hc
      simp only [G3, Finset.mem_insert, Finset.mem_singleton] at hc
      rcases hc with rfl | rfl <;> exact hr _
    · intro r hr
      simp only [G3, Finset.mem_insert, Finset.mem_singleton] at hr
      omega
