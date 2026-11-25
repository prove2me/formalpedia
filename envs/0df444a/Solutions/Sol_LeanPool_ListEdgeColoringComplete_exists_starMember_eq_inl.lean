-- Prove2me | solution 1 for LeanPool.ListEdgeColoringComplete.exists_starMember_eq_inl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T16:48:27.728696+00:00
-- url     : https://prove2.me/submissions/744a4737-934b-468a-a3a0-b4893886022c

module
public import Definitions.Def_LeanPool_ListEdgeColoringComplete_Polynomial
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Definitions.Def_LeanPool_ListEdgeColoringComplete_Main
public import Theorems.Thm_LeanPool_ListEdgeColoringComplete_starMember_of_ne


set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.ListEdgeColoringComplete
open MvPolynomial Finset
variable {V : Type*} [DecidableEq V] {n : ℕ}
namespace LeanPool.ListEdgeColoringComplete
theorem _root_.solution (f : V ≃ Fin n) {v : V} (e : (⊤ : SimpleGraph V).edgeSet)
    (hv : v ∈ (e : Sym2 V)) : ∃ k, starMember f v k = Sum.inl e := by
  obtain ⟨e, he⟩ := e
  obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.mp hv
  have hvw : w ≠ v := fun h => by simp [h] at he
  exact ⟨f w, by rw [starMember_of_ne f hvw]⟩
end LeanPool.ListEdgeColoringComplete
