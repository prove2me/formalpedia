-- Prove2me | solution 1 for GwExact.firstPos_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T20:21:02.489901+00:00
-- url     : https://prove2.me/submissions/a0731cee-a9b4-416b-9b38-22fb7ea274ac

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
theorem _root_.solution (i : ℕ) : firstPos f i ≤ i :=
  Nat.find_min' (⟨i, rfl⟩ : ∃ j, f j = f i) rfl
end GwExact
