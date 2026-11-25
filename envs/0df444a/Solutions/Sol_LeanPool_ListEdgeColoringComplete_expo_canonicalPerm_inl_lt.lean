-- Prove2me | solution 1 for LeanPool.ListEdgeColoringComplete.expo_canonicalPerm_inl_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:15:03.930256+00:00
-- url     : https://prove2.me/submissions/730f6db9-2129-4d6a-9bfe-9f202d6f4a1d

module
public import Definitions.Def_LeanPool_ListEdgeColoringComplete_Polynomial
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Definitions.Def_LeanPool_ListEdgeColoringComplete_Main
public import Theorems.Thm_LeanPool_ListEdgeColoringComplete_canonicalPerm_apply
public import Theorems.Thm_LeanPool_ListEdgeColoringComplete_canonicalRow_spec
public import Theorems.Thm_LeanPool_ListEdgeColoringComplete_expo_inl
public import Theorems.Thm_LeanPool_ListEdgeColoringComplete_targetDegree_lt


set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.ListEdgeColoringComplete
open MvPolynomial Finset
variable {V : Type*} [DecidableEq V] {n : ℕ}
namespace LeanPool.ListEdgeColoringComplete
theorem _root_.solution [Fintype V] (f : V ≃ Fin n)
    (e : (⊤ : SimpleGraph V).edgeSet) : expo f (canonicalPerm f) (Sum.inl e) < n := by
  obtain ⟨e, he⟩ := e
  induction e using Sym2.ind with
  | h a b =>
    have hab : a ≠ b := by simpa using he
    have hfab : f a ≠ f b := fun h => hab (f.injective h)
    rw [expo_inl, canonicalPerm_apply, canonicalPerm_apply]
    have hs := canonicalRow_spec.2.2 (f a) (f b) hfab
    have h2 : 2 ≤ n := by
      have := (f a).isLt; have := (f b).isLt
      have : (f a : ℕ) ≠ f b := fun h => hfab (Fin.ext h)
      omega
    have := targetDegree_lt n (f a) (f b) h2
    omega
end LeanPool.ListEdgeColoringComplete
