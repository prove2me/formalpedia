-- Prove2me | solution 1 for LatinQuarter.Textbook.numCompletions_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:25:03.735517+00:00
-- url     : https://prove2.me/submissions/714a18f9-a5b5-45c9-96c5-60595ee46262

module
public import Mathlib.SetTheory.Cardinal.Finite
public import Definitions.Def_LeanPool_LatinQuarter_Main
public import Definitions.Def_LeanPool_LatinQuarter_Parity
public import Definitions.Def_LeanPool_LatinQuarter_Textbook
public import Theorems.Thm_LatinQuarter_Textbook_completes_iff
public import Theorems.Thm_LatinQuarter_mem_completions
attribute [local simp] LatinQuarter.mem_completions



set_option autoImplicit true
@[expose] public section
public section
open LatinQuarter LatinQuarter.Textbook
namespace LatinQuarter.Textbook
theorem _root_.solution {n : ℕ} {T : Finset (Fin n × Fin n × Fin n)}
    {L : Fin n → Fin n → Fin n} (hL : Completes T L) :
    numCompletions T = (completions (T.image fun t => (t.1, t.2.1)) L).card := by
  rw [numCompletions, ← Nat.card_eq_finsetCard]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun M =>
    (completes_iff hL M).trans mem_completions.symm)
end LatinQuarter.Textbook
