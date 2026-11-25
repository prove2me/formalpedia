-- Prove2me | solution 1 for LeanPool.ListEdgeColoringComplete.eq_canonicalPerm_of_expo_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:15:00.433213+00:00
-- url     : https://prove2.me/submissions/702588e1-36f2-4da0-9a74-2908cfbe01bd

module
public import Definitions.Def_LeanPool_ListEdgeColoringComplete_Certificate
public import Mathlib.Combinatorics.SimpleGraph.LineGraph
public import Mathlib.Combinatorics.Nullstellensatz
public import Mathlib.LinearAlgebra.Vandermonde
public import Definitions.Def_LeanPool_ListEdgeColoringComplete_Polynomial
public import Theorems.Thm_LeanPool_ListEdgeColoringComplete_expo_inr
public import Theorems.Thm_LeanPool_ListEdgeColoringComplete_expo_inl
public import Theorems.Thm_LeanPool_ListEdgeColoringComplete_canonicalPerm_apply
public import Theorems.Thm_LeanPool_ListEdgeColoringComplete_canonicalRow_spec
public import Theorems.Thm_LeanPool_ListEdgeColoringComplete_certificate_unique


set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.ListEdgeColoringComplete
open MvPolynomial Finset
variable {V : Type*} [DecidableEq V] {n : ℕ}
namespace LeanPool.ListEdgeColoringComplete
theorem _root_.solution [Fintype V] (f : V ≃ Fin n) (P : V → Equiv.Perm (Fin n))
    (h : expo f P = expo f (canonicalPerm f)) : P = canonicalPerm f := by
  have hr := certificate_unique (n := n) (fun i j => P (f.symm i) j)
    (fun i => (P (f.symm i)).injective)
    (fun i => by
      have := congrArg (fun m => m (Sum.inr (f.symm i))) h
      simp only [expo_inr, canonicalPerm_apply, Equiv.apply_symm_apply] at this
      rw [this]
      exact canonicalRow_spec.2.1 i)
    (fun i j hij => by
      have hne : f.symm i ≠ f.symm j := fun h' => hij (f.symm.injective h')
      have hab : s(f.symm i, f.symm j) ∈ (⊤ : SimpleGraph V).edgeSet := by simpa using hne
      have := congrArg (fun m => m (Sum.inl ⟨_, hab⟩)) h
      simp only [expo_inl, canonicalPerm_apply, Equiv.apply_symm_apply] at this
      rw [this]
      exact canonicalRow_spec.2.2 i j hij)
  funext u
  ext k
  have := congrFun (congrFun hr (f u)) k
  simpa [canonicalPerm_apply] using congrArg Fin.val this
end LeanPool.ListEdgeColoringComplete
