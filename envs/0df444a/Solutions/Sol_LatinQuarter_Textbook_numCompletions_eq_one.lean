-- Prove2me | solution 1 for LatinQuarter.Textbook.numCompletions_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:24:06.877166+00:00
-- url     : https://prove2.me/submissions/9db3e072-d59e-461b-a91d-81b22eacefb6

module
public import Mathlib.SetTheory.Cardinal.Finite
public import Definitions.Def_LeanPool_LatinQuarter_Main
public import Definitions.Def_LeanPool_LatinQuarter_Parity
public import Definitions.Def_LeanPool_LatinQuarter_Textbook

set_option autoImplicit true
@[expose] public section
public section
open LatinQuarter LatinQuarter.Textbook
namespace LatinQuarter.Textbook
theorem _root_.solution {n : ℕ} {L : Fin n → Fin n → Fin n}
    {T : Finset (Fin n × Fin n × Fin n)} (h : DefiningSet L T) :
    numCompletions T = 1 := by
  rw [numCompletions, Nat.card_eq_one_iff_unique]
  exact ⟨⟨fun a b => Subtype.ext ((h.2 a.1 a.2).trans (h.2 b.1 b.2).symm)⟩,
    ⟨⟨L, h.1⟩⟩⟩
end LatinQuarter.Textbook
