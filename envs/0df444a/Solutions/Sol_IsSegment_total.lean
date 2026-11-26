-- Prove2me | solution 1 for IsSegment_total
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:46:10.174444+00:00
-- url     : https://prove2.me/submissions/1161ca73-9abe-44ed-be4f-2740e919cb7d

import Mathlib.Order.Preorder.Chain
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.WellFoundedSet
import Definitions.Def_ChainBounding_Solution
import Theorems.Thm_IsSegment_of_Subset

set_option autoImplicit true
variable {α : Type*}
open Set IsChain
variable [PartialOrder α]
theorem _root_.solution {A B C : Set α} (hchain : IsChain (· ≤ ·) C) (hA : A ⊑ C) (hB : B ⊑ C) :
    A ⊑ B ∨ B ⊑ A := by
  have hsub : A ⊆ B ∨ B ⊆ A := by
    by_contra h
    have hAB : ¬(A ⊆ B) := fun hsub => h (Or.inl hsub)
    have hBA : ¬(B ⊆ A) := fun hsub => h (Or.inr hsub)
    obtain ⟨a, haA, haB⟩ := Set.not_subset.mp hAB      -- a ∈ A, a ∉ B
    obtain ⟨b, hbB, hbA⟩ := Set.not_subset.mp hBA      -- b ∈ B, b ∉ A
    have hab : a ≠ b := fun hh => haB (by rw [hh]; exact hbB)
    have hcomp : a ≤ b ∨ b ≤ a := hchain (hA.1 haA) (hB.1 hbB) hab
    rcases hcomp with hle | hge
    · exact haB (hB.2 a (hA.1 haA) b hbB hle)   -- a ≤ b puts a ∈ B, contra
    · exact hbA (hA.2 b (hB.1 hbB) a haA hge)   -- b ≤ a puts b ∈ A, contra
  rcases hsub with h | h
  · exact Or.inl (IsSegment_of_Subset B C A hB.1 hA h)
  · exact Or.inr (IsSegment_of_Subset A C B hA.1 hB h)
