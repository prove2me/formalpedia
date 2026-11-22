-- Prove2me | solution 1 for LLexpr.generated_eq_iUnion_combinations
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:27:41.035737+00:00
-- url     : https://prove2.me/submissions/f77cdf31-9644-4b56-bc84-cf3d5401616c

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Disjoint
public import Definitions.Def_LeanPool_OrderClosures_BanLat_LLexpr
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Geometry.Convex.Cone.Pointed
public import Mathlib.Order.Sublattice
public import Mathlib.Order.SupClosed
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Substructures_Sublattice
public import Theorems.Thm_VectorSublattice_coe_toSubmodule
public import Theorems.Thm_VectorSublattice_mem_top
public import Theorems.Thm_VectorSublattice_mem_bot
public import Theorems.Thm_VectorSublattice_subset_generated
public import Theorems.Thm_VectorSublattice_generated_le
public import Theorems.Thm_LLexpr_generated_range_eq_combinations
public import Theorems.Thm_LLexpr_NormalForm_eval_add
public import Theorems.Thm_LLexpr_NormalForm_eval_inf
public import Theorems.Thm_LLexpr_NormalForm_eval_negate
public import Theorems.Thm_LLexpr_NormalForm_eval_smul
public import Theorems.Thm_LLexpr_NormalForm_eval_sup
public import Theorems.Thm_LLexpr_NormalForm_eval_var
public import Theorems.Thm_LLexpr_NormalForm_eval_zero
public import Theorems.Thm_LLexpr_SupLinearCombination_eval_add
public import Theorems.Thm_LLexpr_SupLinearCombination_eval_singleton
public import Theorems.Thm_LLexpr_SupLinearCombination_eval_smul
public import Theorems.Thm_LLexpr_SupLinearCombination_eval_sup
public import Theorems.Thm_LLexpr_eval_add
public import Theorems.Thm_LLexpr_eval_inf
public import Theorems.Thm_LLexpr_eval_reindexExpr
public import Theorems.Thm_LLexpr_eval_smul
public import Theorems.Thm_LLexpr_eval_sup
public import Theorems.Thm_LLexpr_eval_var
public import Theorems.Thm_LLexpr_eval_zero
public import Theorems.Thm_LLexpr_normalize_eval
attribute [local simp] LLexpr.NormalForm.eval_add
attribute [local simp] LLexpr.NormalForm.eval_inf
attribute [local simp] LLexpr.NormalForm.eval_negate
attribute [local simp] LLexpr.NormalForm.eval_smul
attribute [local simp] LLexpr.NormalForm.eval_sup
attribute [local simp] LLexpr.NormalForm.eval_var
attribute [local simp] LLexpr.NormalForm.eval_zero
attribute [local simp] LLexpr.SupLinearCombination.eval_add
attribute [local simp] LLexpr.SupLinearCombination.eval_singleton
attribute [local simp] LLexpr.SupLinearCombination.eval_smul
attribute [local simp] LLexpr.SupLinearCombination.eval_sup
attribute [local simp] LLexpr.eval_add
attribute [local simp] LLexpr.eval_inf
attribute [local simp] LLexpr.eval_reindexExpr
attribute [local simp] LLexpr.eval_smul
attribute [local simp] LLexpr.eval_sup
attribute [local simp] LLexpr.eval_var
attribute [local simp] LLexpr.eval_zero
attribute [local simp] LLexpr.normalize_eval


attribute [local simp] VectorSublattice.coe_toSubmodule
attribute [local simp] VectorSublattice.mem_top
attribute [local simp] VectorSublattice.mem_bot

set_option autoImplicit true
@[expose] public section
public section
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
open LLexpr
variable {n : ℕ}
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
namespace LLexpr
theorem _root_.solution (s : Set X) :
    (VectorSublattice.generated s : Set X)
      = ⋃ (n : ℕ) (x : Fin n → s), combinations ((↑) ∘ x) := by
  let U : Set X := ⋃ (n : ℕ) (x : Fin n → s), combinations ((↑) ∘ x)
  let Y : VectorSublattice X :=
    { toSubmodule :=
        { carrier := U
          zero_mem' := by
            refine Set.mem_iUnion.mpr ⟨0, ?_⟩
            refine Set.mem_iUnion.mpr ⟨Fin.elim0, ?_⟩
            exact ⟨.zero, rfl⟩
          add_mem' := by
            rintro _ _ hx hy
            simp only [U, Set.mem_iUnion] at hx hy ⊢
            obtain ⟨m, x, e₁, rfl⟩ := hx
            obtain ⟨k, y, e₂, rfl⟩ := hy
            refine ⟨m + k, Fin.append x y, .add (reindexExpr (Fin.castAdd k) e₁)
              (reindexExpr (Fin.natAdd m) e₂), ?_⟩
            simp [Function.comp_def]
          smul_mem' := by
            rintro r _ hx
            simp only [U, Set.mem_iUnion] at hx ⊢
            obtain ⟨m, x, e, rfl⟩ := hx
            exact ⟨m, x, .smul r e, rfl⟩ }
      sup_mem' := by
        rintro _ _ hx hy
        simp only [U, Set.mem_iUnion] at hx hy ⊢
        obtain ⟨m, x, e₁, rfl⟩ := hx
        obtain ⟨k, y, e₂, rfl⟩ := hy
        refine ⟨m + k, Fin.append x y, .sup (reindexExpr (Fin.castAdd k) e₁)
          (reindexExpr (Fin.natAdd m) e₂), ?_⟩
        simp [Function.comp_def] }
  have hsY : s ⊆ Y := by
    intro a ha
    change a ∈ U
    refine Set.mem_iUnion.mpr ⟨1, ?_⟩
    refine Set.mem_iUnion.mpr ⟨(fun _ : Fin 1 => ⟨a, ha⟩), ?_⟩
    exact ⟨.var 0, rfl⟩
  refine Set.Subset.antisymm ?_ ?_
  · exact VectorSublattice.generated_le hsY
  · intro a ha
    simp only [Set.mem_iUnion] at ha
    obtain ⟨m, x, hx⟩ := ha
    have hxgen :
        a ∈
          (VectorSublattice.generated (Set.range ((Subtype.val : s → X) ∘ x)) : Set X) := by
      rwa [generated_range_eq_combinations ((Subtype.val : s → X) ∘ x)]
    exact VectorSublattice.generated_le (Y := VectorSublattice.generated s) (fun y hy => by
      obtain ⟨i, rfl⟩ := hy
      exact VectorSublattice.subset_generated s (x i).2) hxgen
end LLexpr
