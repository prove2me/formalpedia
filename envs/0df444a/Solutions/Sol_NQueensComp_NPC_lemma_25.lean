-- Prove2me | solution 1 for NQueensComp.NPC.lemma_25
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T00:35:24.154303+00:00
-- url     : https://prove2.me/submissions/129b5003-3dd7-4686-bea4-59c140702efd

import Mathlib
import Definitions.Def_NQueensComp_NPC_Reductions

open NQueensComp.NPC

theorem shift_inj (δ : ℕ) : Function.Injective (fun q : Queen => q + (δ, 0)) := by
  intro a b h
  simpa using h

theorem attacks_shift (q q' : Queen) (δ : ℕ) :
    Attacks (q + (δ, 0)) (q' + (δ, 0)) ↔ Attacks q q' := by
  obtain ⟨a, b⟩ := q
  obtain ⟨a', b'⟩ := q'
  simp only [Attacks, col, row, sumDiag, diffDiag, ne_eq,
    Prod.mk.injEq, Prod.mk_add_mk, add_zero]
  push_cast
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun h => h1 ⟨by omega, by omega⟩, ?_⟩
    rcases h2 with h | h | h | h
    · exact Or.inl (by omega)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl (by omega)))
    · exact Or.inr (Or.inr (Or.inr (by omega)))
  · rintro ⟨h1, h2⟩
    refine ⟨fun h => h1 ⟨by omega, by omega⟩, ?_⟩
    rcases h2 with h | h | h | h
    · exact Or.inl (by omega)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl (by omega)))
    · exact Or.inr (Or.inr (Or.inr (by omega)))

theorem nonAttacking_shift (Q : Finset Queen) (δ : ℕ) :
    NonAttacking (shiftSet Q (δ, 0)) ↔ NonAttacking Q := by
  simp only [NonAttacking, shiftSet, Finset.mem_image, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]
  constructor
  · intro h q₁ h₁ q₂ h₂
    exact (attacks_shift q₁ q₂ δ).not.mp (h q₁ h₁ q₂ h₂)
  · intro h q₁ h₁ q₂ h₂
    exact (attacks_shift q₁ q₂ δ).not.mpr (h q₁ h₁ q₂ h₂)

theorem solution (G : Inst4) (hG : G.Dp = ∅) (δ : ℕ) (Q : Finset Queen) :
    G.IsSol Q ↔ (G.shift δ).IsSol (shiftSet Q (δ, 0)) := by
  simp only [Inst4.IsSol, Inst4.toInst3, Inst3.IsSol, Inst4.shift, hG, Finset.card_empty,
    add_zero, Finset.empty_subset, true_and, Finset.sdiff_empty, Finset.notMem_empty,
    not_false_eq_true, and_true]
  rw [nonAttacking_shift]
  have hcard : (shiftSet Q (δ, 0)).card = Q.card := by
    unfold shiftSet
    exact Finset.card_image_of_injective _ (shift_inj δ)
  rw [hcard, Finset.card_image_of_injective _ (add_left_injective δ)]
  simp only [shiftSet, Finset.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  constructor
  · rintro ⟨⟨h1, h2, h3⟩, h4⟩
    refine ⟨⟨h1, h2, ?_⟩, ?_⟩
    · intro q hq
      obtain ⟨hc, hr⟩ := h3 q hq
      refine ⟨⟨col q, hc, ?_⟩, ?_⟩
      · obtain ⟨a, b⟩ := q; simp [col]
      · obtain ⟨a, b⟩ := q; simpa [row] using hr
    · intro q hq hmem
      obtain ⟨d, hd, hdq⟩ := hmem
      apply h4 q hq
      obtain ⟨a, b⟩ := q
      simp only [diffDiag, Prod.fst_add, Prod.snd_add, add_zero] at hdq ⊢
      push_cast at hdq
      have : d = (a : ℤ) - b := by linarith
      rwa [this] at hd
  · rintro ⟨⟨h1, h2, h3⟩, h4⟩
    refine ⟨⟨h1, h2, ?_⟩, ?_⟩
    · intro q hq
      obtain ⟨⟨c, hc, hcq⟩, hr⟩ := h3 q hq
      obtain ⟨a, b⟩ := q
      simp only [col, row, Prod.fst_add, Prod.snd_add, add_zero] at hcq hr
      refine ⟨?_, hr⟩
      have : c = a := by omega
      simpa [col, this] using hc
    · intro q hq hd
      apply h4 q hq
      refine ⟨diffDiag q, hd, ?_⟩
      obtain ⟨a, b⟩ := q
      simp only [diffDiag, Prod.fst_add, Prod.snd_add, add_zero]
      push_cast
      ring
