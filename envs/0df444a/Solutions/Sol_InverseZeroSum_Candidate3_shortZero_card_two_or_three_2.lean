-- Prove2me | solution 2 for InverseZeroSum.Candidate3.shortZero_card_two_or_three
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T05:26:54.120487+00:00
-- url     : https://prove2.me/submissions/01e06041-caa6-4d28-8f8b-8f0b19225f5c

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3


theorem solution {n : ℕ} {S : PosSeq n}
    {I : Finset (Fin n)} (h : ShortZero S I) :
    I.card = 2 ∨ I.card = 3 := by
  have hpos := Finset.card_pos.mpr h.1
  have hle := h.2.1
  have hne : I.card ≠ 1 := by
    intro hone; obtain ⟨i,rfl⟩ := Finset.card_eq_one.mp hone
    exact (S i).property (by simpa [posSum] using h.2.2)
  omega
