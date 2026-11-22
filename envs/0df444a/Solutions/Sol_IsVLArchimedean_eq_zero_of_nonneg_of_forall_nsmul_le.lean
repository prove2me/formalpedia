-- Prove2me | solution 1 for IsVLArchimedean.eq_zero_of_nonneg_of_forall_nsmul_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:11:05.602383+00:00
-- url     : https://prove2.me/submissions/5337e9ad-977d-4df6-bc91-fa1527980610

module
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.LinearAlgebra.Dimension.DivisionRing
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.Order.Module.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Push
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Basic

set_option autoImplicit true
@[expose] public section
public section
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
variable (x y : X)
open IsVLArchimedean
omit [VectorLattice X]
namespace IsVLArchimedean
theorem _root_.solution [IsVLArchimedean X] {x y : X}
    (hx : 0 ≤ x) (h : ∀ n : ℕ, n • x ≤ y) : x = 0 :=
  le_antisymm (IsVLArchimedean.le_zero_of_forall_nsmul_le h) hx
end IsVLArchimedean
