-- Prove2me | solution 1 for LatinQuarter.Textbook.definingSet_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:27:14.008329+00:00
-- url     : https://prove2.me/submissions/777da4f9-6e52-4b90-80ef-e6d92b4caf29

module
public import Mathlib.SetTheory.Cardinal.Finite
public import Definitions.Def_LeanPool_LatinQuarter_Main
public import Definitions.Def_LeanPool_LatinQuarter_Parity
public import Definitions.Def_LeanPool_LatinQuarter_Textbook
public import Theorems.Thm_LatinQuarter_Textbook_numCompletions_eq_one
public import Theorems.Thm_LatinQuarter_Textbook_completions_even

set_option autoImplicit true
@[expose] public section
public section
open LatinQuarter LatinQuarter.Textbook
namespace LatinQuarter.Textbook
theorem _root_.solution {n : ℕ} {L : Fin n → Fin n → Fin n}
    {T : Finset (Fin n × Fin n × Fin n)} (h : DefiningSet L T) :
    n * n / 4 ≤ T.card := by
  by_contra hlt
  have he := completions_even T (not_le.mp hlt)
  rw [numCompletions_eq_one h] at he
  exact Nat.not_even_one he
end LatinQuarter.Textbook
