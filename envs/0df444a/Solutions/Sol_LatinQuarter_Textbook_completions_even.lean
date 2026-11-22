-- Prove2me | solution 1 for LatinQuarter.Textbook.completions_even
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:26:29.381548+00:00
-- url     : https://prove2.me/submissions/091bd4ec-5172-4cd7-b9f1-93f905d0649c

module
public import Mathlib.SetTheory.Cardinal.Finite
public import Definitions.Def_LeanPool_LatinQuarter_Main
public import Definitions.Def_LeanPool_LatinQuarter_Parity
public import Definitions.Def_LeanPool_LatinQuarter_Textbook
public import Theorems.Thm_LatinQuarter_Textbook_numCompletions_eq
public import Theorems.Thm_LatinQuarter_completions_card_even


set_option autoImplicit true
@[expose] public section
public section
open LatinQuarter LatinQuarter.Textbook
namespace LatinQuarter.Textbook
theorem _root_.solution {n : ℕ} (T : Finset (Fin n × Fin n × Fin n))
    (hT : T.card < n * n / 4) : Even (numCompletions T) := by
  by_cases h : ∃ L, Completes T L
  · obtain ⟨L, hL⟩ := h
    rw [numCompletions_eq hL]
    exact completions_card_even _ L ((latin_iff L).mp hL.1)
      (lt_of_le_of_lt Finset.card_image_le hT)
  · have : IsEmpty {L : Fin n → Fin n → Fin n // Completes T L} :=
      ⟨fun L => h ⟨L.1, L.2⟩⟩
    rw [numCompletions, Nat.card_of_isEmpty]
    exact Even.zero
end LatinQuarter.Textbook
