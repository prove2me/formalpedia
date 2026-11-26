-- Prove2me | solution 1 for LeanPool.K5MinorFreeChoosability.RIn.exit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:11:12.378167+00:00
-- url     : https://prove2.me/submissions/a5ff77e4-0d80-45cb-bbb8-c9fc8e26c036

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
theorem _root_.solution {P : Set W} (h : RIn G s a b) (haP : a ∈ P) (hbP : b ∉ P) :
    ∃ p q, RIn G (s ∩ P) a p ∧ p ∈ s ∧ p ∈ P ∧ q ∈ s ∧ q ∉ P ∧ G.Adj p q := by
  have key : (∃ p q, RIn G (s ∩ P) a p ∧ p ∈ s ∧ p ∈ P ∧ q ∈ s ∧ q ∉ P ∧ G.Adj p q) ∨
      (b ∈ P ∧ RIn G (s ∩ P) a b) := by
    clear hbP
    induction h with
    | refl => exact Or.inr ⟨haP, refl _⟩
    | @tail c d _ hcd ih =>
      rcases ih with hex | ⟨hc, hac⟩
      · exact Or.inl hex
      · by_cases hd : d ∈ P
        · exact Or.inr ⟨hd, hac.tail hcd.1 ⟨hcd.2.1, hc⟩ ⟨hcd.2.2, hd⟩⟩
        · exact Or.inl ⟨c, d, hac, hcd.2.1, hc, hcd.2.2, hd, hcd.1⟩
  rcases key with hex | ⟨hb, _⟩
  · exact hex
  · exact absurd hb hbP
end LeanPool.K5MinorFreeChoosability.RIn
