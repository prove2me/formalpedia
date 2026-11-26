-- Prove2me | solution 1 for LeanPool.K5MinorFreeChoosability.ConnSet.insert_adj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:29:28.730318+00:00
-- url     : https://prove2.me/submissions/39345748-8e98-4b76-b211-6e3cbb5c84cb

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Basic
public import Mathlib
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Reach
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_RIn_refl
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_RIn_head
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_RIn_symm
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_RIn_mono_set
attribute [local refl] LeanPool.K5MinorFreeChoosability.RIn.refl

set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
variable {W : Type*}
namespace LeanPool.K5MinorFreeChoosability
namespace ConnSet
theorem _root_.solution {G : SimpleGraph W} {s : Set W} (h : ConnSet G s) {a b : W}
    (hb : b ∈ s) (hab : G.Adj a b) : ConnSet G (insert a s) := by
  have hsub : s ⊆ insert a s := Set.subset_insert _ _
  have ha : ∀ x ∈ s, RIn G (insert a s) a x := fun x hx =>
    RIn.head hab (Set.mem_insert _ _) (hsub hb) ((h.2 b hb x hx).mono_set hsub)
  refine ⟨⟨a, Set.mem_insert _ _⟩, fun x hx y hy => ?_⟩
  rcases hx with rfl | hx <;> rcases hy with rfl | hy
  · exact RIn.refl _
  · exact ha y hy
  · exact (ha x hx).symm
  · exact (h.2 x hx y hy).mono_set hsub
end ConnSet
end LeanPool.K5MinorFreeChoosability
