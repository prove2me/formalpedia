-- Prove2me | solution 1 for GwExact.firstPos_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T20:20:59.202412+00:00
-- url     : https://prove2.me/submissions/aeb3b5bf-5251-435f-8f23-1f3a2b5ee2b5

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
theorem _root_.solution (i : ℕ) : f (firstPos f i) = f i :=
  Nat.find_spec (⟨i, rfl⟩ : ∃ j, f j = f i)
end GwExact
