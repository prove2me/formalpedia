-- Prove2me | solution 1 for LeanPool.K5MinorFreeChoosability.RIn.head
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:09:38.176739+00:00
-- url     : https://prove2.me/submissions/4f453e44-a62a-47cb-9148-340399ecb7b8

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
theorem _root_.solution (h : G.Adj a b) (ha : a ∈ s) (hb : b ∈ s) (h₁ : RIn G s b c) : RIn G s a c :=
  Relation.ReflTransGen.head ⟨h, ha, hb⟩ h₁
end LeanPool.K5MinorFreeChoosability.RIn
