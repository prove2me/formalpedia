-- Prove2me | solution 1 for Mader.dbl_union_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:52:04.588243+00:00
-- url     : https://prove2.me/submissions/779e1631-bfc7-4d6a-b935-d428fe27419a

module
public import Mathlib
public import Definitions.Def_MaderLib_MaderAux

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open Mader
variable {V : Type*}
variable (G : SimpleGraph V)
namespace Mader
theorem _root_.solution {S H₁ H₂ : Finset V}
    (hcov : ∀ a ∈ S, ∀ b ∈ S, G.Adj a b → (a ∈ H₁ ∧ b ∈ H₁) ∨ (a ∈ H₂ ∧ b ∈ H₂)) :
    dbl G S ≤ dbl G H₁ + dbl G H₂ := by
  classical
  unfold dbl
  refine (card_le_card ?_).trans (card_union_le _ _)
  rintro ⟨a, b⟩ h
  simp only [mem_filter, mem_product] at h
  simp only [mem_union, mem_filter, mem_product]
  rcases hcov a h.1.1 b h.1.2 h.2 with h' | h'
  · exact Or.inl ⟨h', h.2⟩
  · exact Or.inr ⟨h', h.2⟩
end Mader
