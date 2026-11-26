-- Prove2me | solution 1 for LeanPool.K5MinorFreeChoosability.RIn.avoid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:28:56.558801+00:00
-- url     : https://prove2.me/submissions/404420f9-001a-4742-a5b6-a07c3b403cd4

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Basic
public import Mathlib
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Reach
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_RIn_refl
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_RIn_tail
attribute [local refl] LeanPool.K5MinorFreeChoosability.RIn.refl

set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
variable {W : Type*}
open LeanPool.K5MinorFreeChoosability.RIn
variable {G G' : SimpleGraph W} {s t : Set W} {a b c : W}
namespace LeanPool.K5MinorFreeChoosability.RIn
theorem _root_.solution (h : RIn G s a b) {t : W} (ht : ¬ RIn G s a t) : RIn G (s \ {t}) a b := by
  induction h with
  | refl => exact refl _
  | @tail c d hac hcd ih =>
    have hc : c ≠ t := fun hct => ht (hct ▸ hac)
    have hd : d ≠ t := fun hdt => ht (hdt ▸ RIn.tail hac hcd.1 hcd.2.1 hcd.2.2)
    exact ih.tail hcd.1 ⟨hcd.2.1, hc⟩ ⟨hcd.2.2, hd⟩
end LeanPool.K5MinorFreeChoosability.RIn
