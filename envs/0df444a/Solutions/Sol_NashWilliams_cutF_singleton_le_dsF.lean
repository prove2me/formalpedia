-- Prove2me | solution 1 for NashWilliams.cutF_singleton_le_dsF
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:23:00.767191+00:00
-- url     : https://prove2.me/submissions/632bb12d-b2cd-4269-93b3-f1bc068cf817

module
public import Definitions.Def_NashWilliamsLib_Basic
public import Definitions.Def_NashWilliamsLib_Splitting

set_option autoImplicit true
@[expose] public section
public section
open Finset
open NashWilliams
variable {V ι : Type*} [DecidableEq V]
namespace NashWilliams
theorem _root_.solution {s : V} {ends : ι → V × V} {F : Finset ι} {X : Finset V}
    (h : ∀ l ∈ F, ((ends l).1 = s) ≠ ((ends l).2 = s) → oth s (ends l) ∈ X) :
    cutF ends F {s} ≤ dsF s ends F X := by
  unfold cutF dsF
  refine Finset.card_le_card fun l hl => ?_
  simp only [mem_filter, mem_singleton] at hl ⊢
  refine ⟨hl.1, ?_⟩
  have := h l hl.1 hl.2
  unfold oth at this
  by_cases a1 : (ends l).1 = s
  · simp only [a1, ↓reduceIte] at this
    exact Or.inl ⟨a1, this⟩
  · simp only [a1, ↓reduceIte] at this
    have a2 : (ends l).2 = s := by
      by_contra a2
      exact hl.2 (by simp [a1, a2])
    exact Or.inr ⟨a2, this⟩
end NashWilliams
