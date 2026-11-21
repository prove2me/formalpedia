-- Prove2me | solution 1 for GwExact.notMem_firstPos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T20:23:26.618494+00:00
-- url     : https://prove2.me/submissions/ac373200-3188-4023-bd0f-8bb16a809c57

module
public import Definitions.Def_GwExact_Defs
public import Definitions.Def_GwExact_Clauses
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Fin
public import Definitions.Def_GwExact_Rank
public import Theorems.Thm_GwExact_firstPos_spec
public import Theorems.Thm_GwExact_ne_of_lt_firstPos

set_option autoImplicit true
@[expose] public section
public section
open GwExact
variable {α : Type*} [DecidableEq α] (f : ℕ → α)
namespace GwExact
theorem _root_.solution (i : ℕ) : f (firstPos f i) ∉ (Finset.range (firstPos f i)).image f := by
  intro h
  obtain ⟨j, hj, hfj⟩ := Finset.mem_image.mp h
  exact ne_of_lt_firstPos f (Finset.mem_range.mp hj) (hfj.trans (firstPos_spec f i))
end GwExact
