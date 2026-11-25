-- Prove2me | solution 1 for MatrixTree.det_incMat_sq_of_isTree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T11:37:03.667878+00:00
-- url     : https://prove2.me/submissions/26bbef0e-7b21-494c-b593-95a0b88eed5e

module
public import Mathlib
public import Definitions.Def_MatrixTreeLib_MatrixTree
public import Theorems.Thm_MatrixTree_isUnit_det_incMat_of_isTree

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Matrix Finset
open MatrixTree
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace MatrixTree
theorem _root_.solution (v : V) (g : {u // u ≠ v} → Sym2 V) (hg : ∀ w, ¬ (g w).IsDiag)
    (hT : (fromEdgeSet (Set.range g)).IsTree) : (incMat v g).det ^ 2 = 1 := by
  rcases Int.isUnit_iff.mp (isUnit_det_incMat_of_isTree v g hg hT) with h | h <;>
    rw [h] <;> norm_num
end MatrixTree
