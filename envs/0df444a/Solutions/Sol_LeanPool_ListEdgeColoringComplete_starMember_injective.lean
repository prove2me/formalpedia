-- Prove2me | solution 1 for LeanPool.ListEdgeColoringComplete.starMember_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T16:48:43.971744+00:00
-- url     : https://prove2.me/submissions/9cf38c2d-d0dd-4aa7-87de-b247dbd7cd26

module
public import Definitions.Def_LeanPool_ListEdgeColoringComplete_Certificate
public import Mathlib.Combinatorics.SimpleGraph.LineGraph
public import Mathlib.Combinatorics.Nullstellensatz
public import Mathlib.LinearAlgebra.Vandermonde
public import Definitions.Def_LeanPool_ListEdgeColoringComplete_Polynomial

set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.ListEdgeColoringComplete
open MvPolynomial Finset
variable {V : Type*} [DecidableEq V] {n : ℕ}
namespace LeanPool.ListEdgeColoringComplete
theorem _root_.solution (f : V ≃ Fin n) (u : V) :
    Function.Injective (starMember f u) := by
  intro k k' h
  unfold starMember at h
  split_ifs at h with h1 h2 h2
  · exact f.symm.injective (h1.trans h2.symm)
  · simp only [Sum.inl.injEq, Subtype.mk.injEq, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq,
      Prod.swap_prod_mk] at h
    rcases h with ⟨-, h⟩ | ⟨-, h⟩
    · exact f.symm.injective h
    · exact absurd h h1
end LeanPool.ListEdgeColoringComplete
