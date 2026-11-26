-- Prove2me | solution 1 for LeanPool.K5MinorFreeChoosability.RIn.tail
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:09:37.257912+00:00
-- url     : https://prove2.me/submissions/524f6027-cd71-4c39-94ca-97f40d36eb19

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
theorem _root_.solution (h₁ : RIn G s a b) (h : G.Adj b c) (hb : b ∈ s) (hc : c ∈ s) : RIn G s a c :=
  Relation.ReflTransGen.tail h₁ ⟨h, hb, hc⟩
end LeanPool.K5MinorFreeChoosability.RIn
