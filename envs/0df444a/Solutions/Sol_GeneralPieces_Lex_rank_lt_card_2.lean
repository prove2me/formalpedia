-- Prove2me | solution 2 for GeneralPieces.Lex.rank_lt_card
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T00:33:01.82363+00:00
-- url     : https://prove2.me/submissions/0fd9b5ba-3e84-4842-8e47-32c858ca6539

import Mathlib.Combinatorics.Colex
import Mathlib.Data.List.Lex

set_option autoImplicit false

open Finset

variable {α β : Type} [LinearOrder β] [DecidableRel fun a b : β => a < b]
  (S : Finset α) (f : α → β)

theorem solution {a : α} (ha : a ∈ S) : #{c ∈ S | f c < f a} < #S := by
  apply card_lt_card
  refine ⟨filter_subset _ _, ?_⟩
  intro hsub
  exact lt_irrefl _ (mem_filter.1 (hsub ha)).2
