-- Prove2me | solution 1 for LLexpr.SupLinearCombination.eval_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:15:51.395968+00:00
-- url     : https://prove2.me/submissions/fe764398-bfc7-421d-8f9f-a257e375bc28

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Basic
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Definitions.Def_LeanPool_OrderClosures_BanLat_LLexpr
public import Theorems.Thm_LLexpr_eval_zero
public import Theorems.Thm_LLexpr_eval_var
public import Theorems.Thm_LLexpr_eval_add
public import Theorems.Thm_LLexpr_eval_smul
public import Theorems.Thm_LLexpr_eval_sup
public import Theorems.Thm_LLexpr_eval_inf
public import Theorems.Thm_LLexpr_eval_reindexExpr
public import Theorems.Thm_LLexpr_SupLinearCombination_eval_singleton
attribute [local simp] LLexpr.eval_zero
attribute [local simp] LLexpr.eval_var
attribute [local simp] LLexpr.eval_add
attribute [local simp] LLexpr.eval_smul
attribute [local simp] LLexpr.eval_sup
attribute [local simp] LLexpr.eval_inf
attribute [local simp] LLexpr.eval_reindexExpr
attribute [local simp] LLexpr.SupLinearCombination.eval_singleton
section
@[expose] public section
namespace LLexpr
open scoped BigOperators
variable {n : ℕ}
section Evaluation
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
end Evaluation
section Combinations
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
end Combinations
private theorem sup'_add_right {ι X : Type*} [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] (s : Finset ι) (hs : s.Nonempty) (f : ι → X) (a : X) :
    s.sup' hs f + a = s.sup' hs (fun i => f i + a) :=
  map_finset_sup' (OrderIso.addRight a) hs f
private theorem add_left_sup' {ι X : Type*} [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] (s : Finset ι) (hs : s.Nonempty) (f : ι → X) (a : X) :
    a + s.sup' hs f = s.sup' hs (fun i => a + f i) :=
  map_finset_sup' (OrderIso.addLeft a) hs f
namespace SupLinearCombination
@[simp] private theorem linearCombination_zero_coeff {X : Type*} [AddCommGroup X]
    [Module ℝ X] (x : Fin n → X) :
    Fintype.linearCombination ℝ x (fun _ : Fin n => 0) = 0 := by
  change Fintype.linearCombination ℝ x (0 : Fin n → ℝ) = 0
  exact map_zero (Fintype.linearCombination ℝ x)
end SupLinearCombination
namespace NormalForm
end NormalForm
end LLexpr
end
end

set_option autoImplicit true
@[expose] public section
public section
open LLexpr
open scoped BigOperators
variable {n : ℕ}
open LLexpr.SupLinearCombination
namespace LLexpr.SupLinearCombination
theorem _root_.solution {X : Type*} [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [VectorLattice X] (A B : SupLinearCombination n)
    (x : Fin n → X) :
    (A.add B).eval x = A.eval x + B.eval x := by
  classical
  unfold eval add
  rw [Finset.sup'_image₂_left]
  simp only [map_add]
  simp_rw [← add_left_sup' B.coeffs B.nonempty (fun b => Fintype.linearCombination ℝ x b)]
  rw [← sup'_add_right A.coeffs A.nonempty (fun a => Fintype.linearCombination ℝ x a)]
end LLexpr.SupLinearCombination
