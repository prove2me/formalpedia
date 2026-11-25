-- Prove2me | solution 1 for MatrixTree.det_incMat_eq_zero_of_not_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T11:10:28.132358+00:00
-- url     : https://prove2.me/submissions/ae8e8364-a1a5-41fb-b8f6-c24ed3a0c5cf

module
public import Mathlib
public import Definitions.Def_MatrixTreeLib_MatrixTree

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Matrix Finset
open MatrixTree
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace MatrixTree
theorem _root_.solution (v : V) (g : {u // u ≠ v} → Sym2 V)
    (hg : ¬ Function.Injective g) : (incMat v g).det = 0 := by
  simp only [Function.Injective, not_forall] at hg
  obtain ⟨i, j, hij, hne⟩ := hg
  exact det_zero_of_column_eq hne (fun l => by simp [incMat, hij])
end MatrixTree
