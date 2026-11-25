-- Prove2me | solution 1 for LeanPool.Vizing.PEC.col_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:07:24.60162+00:00
-- url     : https://prove2.me/submissions/35a24a09-4e98-4d35-9672-270247d2d76d

module
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Tauto
public import Definitions.Def_LeanPool_Vizing_Basic

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open LeanPool LeanPool.Vizing
variable {V : Type*} [DecidableEq V] {C : Type*}
open LeanPool.Vizing.PEC
variable {G : SimpleGraph V}
omit [DecidableEq V]
namespace LeanPool.Vizing.PEC
theorem _root_.solution (c : PEC G C) (u : V) : c.col u u = none := by
  cases h : c.col u u with
  | none => rfl
  | some γ => exact absurd (c.col_adj h) (G.irrefl)
end LeanPool.Vizing.PEC
