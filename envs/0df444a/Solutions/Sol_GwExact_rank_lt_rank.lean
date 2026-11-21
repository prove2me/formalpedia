-- Prove2me | solution 1 for GwExact.rank_lt_rank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T20:23:55.773198+00:00
-- url     : https://prove2.me/submissions/75afdfed-3e2e-49e8-88e5-acec24e50790

module
public import Definitions.Def_GwExact_Defs
public import Definitions.Def_GwExact_Clauses
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Fin
public import Definitions.Def_GwExact_Rank
public import Theorems.Thm_GwExact_numCols_mono
public import Theorems.Thm_GwExact_numCols_succ_of_notMem
public import Theorems.Thm_GwExact_notMem_firstPos

set_option autoImplicit true
@[expose] public section
public section
open GwExact
variable {α : Type*} [DecidableEq α] (f : ℕ → α)
namespace GwExact
theorem _root_.solution {i i' : ℕ} (h : firstPos f i < firstPos f i') : rank f i < rank f i' := by
  have h1 := numCols_succ_of_notMem f (notMem_firstPos f i)
  have h2 := numCols_mono f (show firstPos f i + 1 ≤ firstPos f i' by omega)
  unfold rank
  omega
end GwExact
