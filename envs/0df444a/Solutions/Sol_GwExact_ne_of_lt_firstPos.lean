-- Prove2me | solution 1 for GwExact.ne_of_lt_firstPos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T20:21:16.711596+00:00
-- url     : https://prove2.me/submissions/57c13d82-eecb-433b-95bd-f29a307f291f

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
variable {α : Type*} [DecidableEq α] (f : ℕ → α)
namespace GwExact
theorem _root_.solution {i j : ℕ} (h : j < firstPos f i) : f j ≠ f i :=
  Nat.find_min (⟨i, rfl⟩ : ∃ j, f j = f i) h
end GwExact
