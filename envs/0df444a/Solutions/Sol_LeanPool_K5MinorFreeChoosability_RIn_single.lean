-- Prove2me | solution 1 for LeanPool.K5MinorFreeChoosability.RIn.single
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:28:05.139966+00:00
-- url     : https://prove2.me/submissions/d8d0f120-1032-447a-ac1d-232e677a9c94

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Basic
public import Mathlib
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Reach

set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
variable {W : Type*}
open LeanPool.K5MinorFreeChoosability.RIn
variable {G G' : SimpleGraph W} {s t : Set W} {a b c : W}
namespace LeanPool.K5MinorFreeChoosability.RIn
theorem _root_.solution (h : G.Adj a b) (ha : a ∈ s) (hb : b ∈ s) : RIn G s a b :=
  Relation.ReflTransGen.single ⟨h, ha, hb⟩
end LeanPool.K5MinorFreeChoosability.RIn
