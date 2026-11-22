-- Prove2me | solution 1 for LLexpr.generated_range_eq_combinations
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:25:38.785958+00:00
-- url     : https://prove2.me/submissions/cde4cb31-1d94-4822-9729-89bc05acf882

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Disjoint
public import Definitions.Def_LeanPool_OrderClosures_BanLat_LLexpr
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Geometry.Convex.Cone.Pointed
public import Mathlib.Order.Sublattice
public import Mathlib.Order.SupClosed
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Substructures_Sublattice
public import Theorems.Thm_VectorSublattice_subset_generated
public import Theorems.Thm_VectorSublattice_generated_le

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
theorem _root_.solution (x : Fin n → X) :
    (VectorSublattice.generated (Set.range x) : Set X)
      = combinations x := by
  let Y : VectorSublattice X :=
    { toSubmodule :=
        { carrier := combinations x
          zero_mem' := ⟨.zero, rfl⟩
          add_mem' := by
            rintro _ _ ⟨e₁, rfl⟩ ⟨e₂, rfl⟩
            exact ⟨.add e₁ e₂, rfl⟩
          smul_mem' := by
            rintro r _ ⟨e, rfl⟩
            exact ⟨.smul r e, rfl⟩ }
      sup_mem' := by
        rintro _ _ ⟨e₁, rfl⟩ ⟨e₂, rfl⟩
        exact ⟨.sup e₁ e₂, rfl⟩ }
  refine Set.Subset.antisymm ?_ ?_
  · change (VectorSublattice.generated (Set.range x) : Set X) ⊆ (Y : Set X)
    exact VectorSublattice.generated_le (Y := Y) (by
      rintro _ ⟨i, rfl⟩
      exact ⟨.var i, rfl⟩)
  · rintro _ ⟨e, rfl⟩
    induction e with
    | zero =>
        exact (VectorSublattice.generated (Set.range x)).toSubmodule.zero_mem
    | var i =>
        exact VectorSublattice.subset_generated (Set.range x) ⟨i, rfl⟩
    | add e₁ e₂ he₁ he₂ =>
        exact (VectorSublattice.generated (Set.range x)).toSubmodule.add_mem he₁ he₂
    | smul r e he =>
        exact (VectorSublattice.generated (Set.range x)).toSubmodule.smul_mem r he
    | sup e₁ e₂ he₁ he₂ =>
        exact (VectorSublattice.generated (Set.range x)).sup_mem he₁ he₂
    | inf e₁ e₂ he₁ he₂ =>
        exact (VectorSublattice.generated (Set.range x)).inf_mem he₁ he₂
end LLexpr
