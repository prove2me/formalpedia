-- Prove2me | solution 1 for LeanPool.K5MinorFreeChoosability.restrict_adj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:09:37.746339+00:00
-- url     : https://prove2.me/submissions/ae9cba87-9724-4575-929e-5a7bca872538

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Basic
public import Mathlib
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Reach

set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
variable {W : Type*}
namespace LeanPool.K5MinorFreeChoosability
theorem _root_.solution {G : SimpleGraph W} {s : Set W} {a b : W} :
    (restrict G s).Adj a b ↔ G.Adj a b ∧ a ∈ s ∧ b ∈ s := Iff.rfl
end LeanPool.K5MinorFreeChoosability
