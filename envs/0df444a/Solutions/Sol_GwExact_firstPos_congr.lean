-- Prove2me | solution 1 for GwExact.firstPos_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T20:23:14.900163+00:00
-- url     : https://prove2.me/submissions/88f975d9-9a32-499a-869a-5d19921453f7

module
public import Definitions.Def_GwExact_Defs
public import Definitions.Def_GwExact_Clauses
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Fin
public import Definitions.Def_GwExact_Rank
public import Theorems.Thm_GwExact_firstPos_spec

set_option autoImplicit true
@[expose] public section
public section
open GwExact
variable {α : Type*} [DecidableEq α] (f : ℕ → α)
namespace GwExact
theorem _root_.solution {i i' : ℕ} (h : f i = f i') : firstPos f i = firstPos f i' :=
  le_antisymm (Nat.find_min' _ ((firstPos_spec f i').trans h.symm))
    (Nat.find_min' _ ((firstPos_spec f i).trans h))
end GwExact
