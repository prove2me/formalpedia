-- Prove2me | solution 1 for LeanPool.ListEdgeColoringComplete.expo_inl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:10:46.026564+00:00
-- url     : https://prove2.me/submissions/7db189c3-6832-4524-9402-de0e7d329bcc

module
public import Definitions.Def_LeanPool_ListEdgeColoringComplete_Certificate
public import Mathlib.Combinatorics.SimpleGraph.LineGraph
public import Mathlib.Combinatorics.Nullstellensatz
public import Mathlib.LinearAlgebra.Vandermonde
public import Definitions.Def_LeanPool_ListEdgeColoringComplete_Polynomial
public import Theorems.Thm_LeanPool_ListEdgeColoringComplete_starMember_eq_inl

set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.ListEdgeColoringComplete
open MvPolynomial Finset
variable {V : Type*} [DecidableEq V] {n : ℕ}
namespace LeanPool.ListEdgeColoringComplete
theorem _root_.solution [Fintype V] (f : V ≃ Fin n) (P : V → Equiv.Perm (Fin n)) (a b : V)
    (hab : s(a, b) ∈ (⊤ : SimpleGraph V).edgeSet) :
    expo f P (Sum.inl ⟨s(a, b), hab⟩) = P a (f b) + P b (f a) := by
  have hne : a ≠ b := by simpa using hab
  simp only [expo, Finsupp.finsetSum_apply, Finsupp.single_apply, starMember_eq_inl]
  rw [Fintype.sum_eq_add a b hne, Fintype.sum_eq_single (f b), Fintype.sum_eq_single (f a)]
  · simp [hne, Ne.symm hne]
  · intro k hk
    simp [hk, Ne.symm hne]
  · intro k hk
    simp [hk, hne]
  · rintro w ⟨hwa, hwb⟩
    exact Finset.sum_eq_zero fun k _ => by simp [hwa, hwb]
end LeanPool.ListEdgeColoringComplete
