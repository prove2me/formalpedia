-- Prove2me | solution 1 for GwExact.lt_of_good
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T20:23:52.94418+00:00
-- url     : https://prove2.me/submissions/38520466-0fec-447c-ba96-e8801ed1483f

module
public import Definitions.Def_GwExact_Defs
public import Definitions.Def_GwExact_Clauses
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Fin
public import Definitions.Def_GwExact_Rank

set_option autoImplicit true
@[expose] public section
public section
open GwExact
namespace GwExact
theorem _root_.solution {r l n : ℕ} {c : ℕ → Fin r} (hc : IsGoodExactColouring r l n c) {m : ℕ}
    (hm : GWProperty r l m) : n < m := by
  by_contra h
  exact hm n (not_lt.mp h) c hc
end GwExact
