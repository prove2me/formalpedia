-- Prove2me | solution 1 for LeanPool.K5MinorFreeChoosability.connSet_reach
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:29:29.203122+00:00
-- url     : https://prove2.me/submissions/0067f217-06d8-46eb-ad08-fd2e823a7aea

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Basic
public import Mathlib
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Reach
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_RIn_refl
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_RIn_trans
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_RIn_tail
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_RIn_symm
attribute [local refl] LeanPool.K5MinorFreeChoosability.RIn.refl

set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
variable {W : Type*}
namespace LeanPool.K5MinorFreeChoosability
theorem _root_.solution (G : SimpleGraph W) (s : Set W) {a : W} (ha : a ∈ s) :
    ConnSet G {x | x ∈ s ∧ RIn G s a x} := by
  have key : ∀ x, RIn G s a x → RIn G {x | x ∈ s ∧ RIn G s a x} a x := by
    intro x hx
    induction hx with
    | refl => exact RIn.refl _
    | @tail c d hac hcd ih =>
      exact RIn.tail ih hcd.1 ⟨hcd.2.1, hac⟩ ⟨hcd.2.2, RIn.tail hac hcd.1 hcd.2.1 hcd.2.2⟩
  exact ⟨⟨a, ha, RIn.refl _⟩, fun x hx y hy => (key x hx.2).symm.trans (key y hy.2)⟩
end LeanPool.K5MinorFreeChoosability
