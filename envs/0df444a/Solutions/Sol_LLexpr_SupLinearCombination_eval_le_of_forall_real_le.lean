-- Prove2me | solution 1 for LLexpr.SupLinearCombination.eval_le_of_forall_real_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:17:20.554389+00:00
-- url     : https://prove2.me/submissions/34a0a1af-f6d3-4088-ab3a-01a0908710d3

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
public import Theorems.Thm_LLexpr_SupLinearCombination_eval_add
public import Theorems.Thm_LLexpr_SupLinearCombination_eval_sup
public import Theorems.Thm_LLexpr_SupLinearCombination_eval_smul
attribute [local simp] LLexpr.eval_zero
attribute [local simp] LLexpr.eval_var
attribute [local simp] LLexpr.eval_add
attribute [local simp] LLexpr.eval_smul
attribute [local simp] LLexpr.eval_sup
attribute [local simp] LLexpr.eval_inf
attribute [local simp] LLexpr.eval_reindexExpr
attribute [local simp] LLexpr.SupLinearCombination.eval_singleton
attribute [local simp] LLexpr.SupLinearCombination.eval_add
attribute [local simp] LLexpr.SupLinearCombination.eval_sup
attribute [local simp] LLexpr.SupLinearCombination.eval_smul
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
namespace SupLinearCombination
@[simp] private theorem linearCombination_zero_coeff {X : Type*} [AddCommGroup X]
    [Module ℝ X] (x : Fin n → X) :
    Fintype.linearCombination ℝ x (fun _ : Fin n => 0) = 0 := by
  change Fintype.linearCombination ℝ x (0 : Fin n → ℝ) = 0
  exact map_zero (Fintype.linearCombination ℝ x)
private theorem continuousLinearMap_apply_eq_linearCombination (f : StrongDual ℝ (Fin n → ℝ))
    (a : Fin n → ℝ) :
    f a = Fintype.linearCombination ℝ
      (fun i => f (Pi.single i (1 : ℝ) : Fin n → ℝ)) a := by
  classical
  have ha : a = ∑ i, a i • (Pi.single i (1 : ℝ) : Fin n → ℝ) := by
    funext j
    simp [Pi.single_apply, Finset.sum_apply]
  calc
    f a = f (∑ i, a i • (Pi.single i (1 : ℝ) : Fin n → ℝ)) := by rw [← ha]
    _ = ∑ i, f (a i • (Pi.single i (1 : ℝ) : Fin n → ℝ)) := by rw [map_sum]
    _ = ∑ i, a i * f (Pi.single i (1 : ℝ) : Fin n → ℝ) := by simp
    _ = Fintype.linearCombination ℝ
        (fun i => f (Pi.single i (1 : ℝ) : Fin n → ℝ)) a := by
      simp [Fintype.linearCombination_apply, smul_eq_mul]
private theorem mem_convexHull_of_forall_le_sup (p : Fin n → ℝ)
    (S : Finset (Fin n → ℝ)) (hS : S.Nonempty)
    (h : ∀ r : Fin n → ℝ,
      Fintype.linearCombination ℝ r p ≤ S.sup' hS (Fintype.linearCombination ℝ r)) :
    p ∈ convexHull ℝ (S : Set (Fin n → ℝ)) := by
  classical
  by_contra hp
  obtain ⟨f, u, hfp, hsep⟩ := _root_.geometric_hahn_banach_point_closed
    (E := Fin n → ℝ)
    (convex_convexHull ℝ (S : Set (Fin n → ℝ))) (S.finite_toSet.isClosed_convexHull ℝ) hp
  let c : Fin n → ℝ := fun i => f (Pi.single i (1 : ℝ) : Fin n → ℝ)
  let r : Fin n → ℝ := fun i => -c i
  have hf_eval : ∀ a : Fin n → ℝ, f a = Fintype.linearCombination ℝ c a := fun a =>
    continuousLinearMap_apply_eq_linearCombination f a
  have hsup_lt :
      S.sup' hS (Fintype.linearCombination ℝ r) < Fintype.linearCombination ℝ r p := by
    rw [Finset.sup'_lt_iff]
    intro q hq
    have hqconv : q ∈ convexHull ℝ (S : Set (Fin n → ℝ)) :=
      subset_convexHull ℝ (S : Set (Fin n → ℝ)) hq
    have hqsep := hsep q hqconv
    have : -f q < -f p := by
      simpa using neg_lt_neg (hfp.trans hqsep)
    have hq_eval : Fintype.linearCombination ℝ r q = -f q := by
      rw [hf_eval q]
      simp [Fintype.linearCombination_apply, r, c, Finset.sum_neg_distrib, smul_eq_mul]
    have hp_eval : Fintype.linearCombination ℝ r p = -f p := by
      rw [hf_eval p]
      simp [Fintype.linearCombination_apply, r, c, Finset.sum_neg_distrib, smul_eq_mul]
    simpa [hq_eval, hp_eval] using this
  exact (not_lt_of_ge (h r)) hsup_lt
private theorem linearCombination_le_eval_of_mem_convexHull {X : Type*} [AddCommGroup X]
    [Lattice X] [IsOrderedAddMonoid X] [VectorLattice X] (B : SupLinearCombination n)
    {p : Fin n → ℝ} (hp : p ∈ convexHull ℝ (B.coeffs : Set (Fin n → ℝ)))
    (x : Fin n → X) :
    Fintype.linearCombination ℝ x p ≤ B.eval x := by
  classical
  rw [Finset.mem_convexHull'] at hp
  obtain ⟨w, hw_nonneg, hw_sum, hw_eq⟩ := hp
  calc
    Fintype.linearCombination ℝ x p =
        Fintype.linearCombination ℝ x (∑ q ∈ B.coeffs, w q • q) := by
      rw [hw_eq]
    _ = ∑ q ∈ B.coeffs, w q • Fintype.linearCombination ℝ x q := by
      simp
    _ ≤ ∑ q ∈ B.coeffs, w q • B.eval x := by
      refine Finset.sum_le_sum fun q hq => ?_
      exact smul_le_smul_of_nonneg_left
        (Finset.le_sup' (Fintype.linearCombination ℝ x) hq) (hw_nonneg q hq)
    _ = B.eval x := by
      rw [← Finset.sum_smul, hw_sum, one_smul]
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
theorem _root_.solution {X : Type*} [AddCommGroup X]
    [Lattice X] [IsOrderedAddMonoid X] [VectorLattice X] (A B : SupLinearCombination n)
    (h : ∀ r : Fin n → ℝ, A.eval r ≤ B.eval r) (x : Fin n → X) :
    A.eval x ≤ B.eval x := by
  classical
  unfold eval
  refine Finset.sup'_le A.nonempty (Fintype.linearCombination ℝ x) fun p hp => ?_
  exact linearCombination_le_eval_of_mem_convexHull B
    (mem_convexHull_of_forall_le_sup p B.coeffs B.nonempty fun r =>
      (Finset.le_sup' (Fintype.linearCombination ℝ r) hp).trans (h r)) x
end LLexpr.SupLinearCombination
