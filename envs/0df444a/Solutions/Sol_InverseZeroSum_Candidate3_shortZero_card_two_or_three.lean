-- Prove2me | solution 1 for InverseZeroSum.Candidate3.shortZero_card_two_or_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:25:57.119038+00:00
-- url     : https://prove2.me/submissions/f4051cb3-e38e-4bc8-9d2f-aaa3f98568d5

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
public import Theorems.Thm_InverseZeroSum_Candidate3_singleton_not_shortZero

set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3
namespace InverseZeroSum.Candidate3
theorem _root_.solution {n : ℕ} {S : PosSeq n}
    {I : Finset (Fin n)} (h : ShortZero S I) :
    I.card = 2 ∨ I.card = 3 := by
  have hpos : 0 < I.card := Finset.card_pos.mpr h.1
  have hle : I.card ≤ 3 := h.2.1
  have hne : I.card ≠ 1 := by
    intro hone
    obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hone
    exact singleton_not_shortZero S i h
  omega
end InverseZeroSum.Candidate3
