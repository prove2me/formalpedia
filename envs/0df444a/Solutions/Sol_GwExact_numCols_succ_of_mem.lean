-- Prove2me | solution 1 for GwExact.numCols_succ_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T20:23:23.839204+00:00
-- url     : https://prove2.me/submissions/5886f7c7-d82e-469f-9bee-1c1de412e0f7

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
theorem _root_.solution {m : ℕ} (h : f m ∈ (Finset.range m).image f) :
    numCols f (m + 1) = numCols f m := by
  rw [numCols, numCols, Finset.range_add_one, Finset.image_insert, Finset.insert_eq_of_mem h]
end GwExact
