-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.net0O2_genF_locals_of_W
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-29T04:53:53.256078+00:00
-- url     : https://prove2.me/submissions/40057072-8960-4005-9479-cda2baf9e6d3

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNet
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

open IntMul.Kappa.R8.Bit.Oppbank.NB

private def ChHas (ℓ : ℕ) (ch : LChunk) : Prop :=
  (∃ mv ∈ ch.2.1, mv.1 = ℓ) ∨ (∃ p ∈ ch.2.2, p.1 = ℓ ∨ p.2 = ℓ)

private lemma mvF_snd {c : ℕ} {acc : (ℕ → ℕ) × List (ℕ × ℕ)} {w : ℕ} {p : ℕ × ℕ}
    (h : p ∈ (mvF c acc w).2) : p ∈ acc.2 ∨ p = (w, acc.1 w) := by
  by_cases hc : acc.1 w = c
  · simp only [mvF, if_pos hc] at h
    exact Or.inl h
  · simp only [mvF, if_neg hc, List.mem_cons] at h
    tauto

private lemma foldl_mvF_snd {c : ℕ} (l : List ℕ) (acc : (ℕ → ℕ) × List (ℕ × ℕ)) :
    ∀ p ∈ (l.foldl (mvF c) acc).2, p ∈ acc.2 ∨ p.1 ∈ l := by
  induction l generalizing acc with
  | nil => intro p hp; exact Or.inl hp
  | cons w l ih =>
    intro p hp
    simp only [List.foldl_cons] at hp
    rcases ih (mvF c acc w) p hp with h | h
    · rcases mvF_snd h with h' | h'
      · exact Or.inl h'
      · exact Or.inr (by simp [h'])
    · exact Or.inr (by simp [h])

private lemma mem_genStepF_snd {acc : (ℕ → ℕ) × List LChunk} {i : LInstr} {ch : LChunk}
    (h : ch ∈ (genStepF acc i).2) :
    ch ∈ acc.2 ∨ (ch.2.2 = i.2.2 ∧ ∀ mv ∈ ch.2.1, mv.1 ∈ i.2.1) := by
  simp only [genStepF, List.mem_cons] at h
  rcases h with rfl | h
  · refine Or.inr ⟨rfl, ?_⟩
    intro mv hmv
    have hmv' : mv ∈ (i.2.1.foldl (mvF i.1) (acc.1, [])).2 := by
      simpa using hmv
    rcases foldl_mvF_snd i.2.1 (acc.1, []) mv hmv' with hnil | hmem
    · simp at hnil
    · exact hmem
  · exact Or.inl h

private lemma fold_genStepF_mem (W : List LInstr) (acc : (ℕ → ℕ) × List LChunk) (ℓ : ℕ) :
    ∀ ch : LChunk, ch ∈ (W.foldl genStepF acc).2 → ChHas ℓ ch →
    (∃ ch' ∈ acc.2, ChHas ℓ ch') ∨
      ∃ i ∈ W, ℓ ∈ i.2.1 ∨ ∃ p ∈ i.2.2, p.1 = ℓ ∨ p.2 = ℓ := by
  induction W generalizing acc with
  | nil => intro ch hch hP; exact Or.inl ⟨ch, hch, hP⟩
  | cons i W ih =>
    intro ch hch hP
    simp only [List.foldl_cons] at hch
    rcases ih (genStepF acc i) ch hch hP with ⟨ch', hch', hP'⟩ | h
    · rcases mem_genStepF_snd hch' with hacc | ⟨h22, hmv⟩
      · exact Or.inl ⟨ch', hacc, hP'⟩
      · refine Or.inr ⟨i, by simp, ?_⟩
        rcases hP' with ⟨mv, hmv', rfl⟩ | ⟨p, hp, hp'⟩
        · exact Or.inl (hmv mv hmv')
        · exact Or.inr ⟨p, by rw [← h22]; exact hp, hp'⟩
    · obtain ⟨i', hi', hPi'⟩ := h
      exact Or.inr ⟨i', by simp [hi'], hPi'⟩

theorem solution (f : ℕ → ℕ) (W : List LInstr) (ℓ : ℕ)
    (hℓ : ∃ ch ∈ (genF f W).2,
      (∃ mv ∈ ch.2.1, mv.1 = ℓ) ∨ (∃ p ∈ ch.2.2, p.1 = ℓ ∨ p.2 = ℓ)) :
    ∃ i ∈ W, ℓ ∈ i.2.1 ∨ ∃ p ∈ i.2.2, p.1 = ℓ ∨ p.2 = ℓ := by
  obtain ⟨ch, hch, hP⟩ := hℓ
  simp only [genF, List.mem_reverse] at hch
  rcases fold_genStepF_mem W (f, []) ℓ ch hch hP with ⟨ch', hch', _⟩ | h
  · simp at hch'
  · exact h
