-- Prove2me | solution 1 for LeanPool.Vizing.PEC.kempeGraph_adj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:55:32.469802+00:00
-- url     : https://prove2.me/submissions/ff52bd60-2aa5-4d80-a7eb-6a057d824902

module
public import Definitions.Def_LeanPool_Vizing_Endpoints
public import Definitions.Def_LeanPool_Vizing_Kempe

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open LeanPool LeanPool.Vizing
open LeanPool.Vizing.PEC
variable {V : Type*} [Fintype V] [DecidableEq V] {C : Type*} [DecidableEq C]
  {G : SimpleGraph V}
omit [Fintype V] [DecidableEq V] [DecidableEq C]
namespace LeanPool.Vizing.PEC
theorem _root_.solution {c : PEC G C} {a b : C} {u v : V} :
    (c.kempeGraph a b).Adj u v ↔ u ≠ v ∧ (c.col u v = some a ∨ c.col u v = some b) := Iff.rfl
end LeanPool.Vizing.PEC
