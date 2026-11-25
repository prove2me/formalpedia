-- Prove2me | solution 1 for MatrixTree.det_mul_eq_sum_fun
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T11:06:39.087307+00:00
-- url     : https://prove2.me/submissions/5646980d-9031-488e-9da5-a542d3cbc93d

module
public import Mathlib
public import Definitions.Def_MatrixTreeLib_MatrixTree

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Matrix Finset
open MatrixTree
namespace MatrixTree
theorem _root_.solution {R : Type*} [CommRing R] {m k : ℕ} (A : Matrix (Fin m) (Fin k) R)
    (B : Matrix (Fin k) (Fin m) R) :
    (A * B).det = ∑ p : Fin m → Fin k, (A.submatrix id p).det * ∏ i, B (p i) i := by
  simp only [det_apply', mul_apply, prod_univ_sum, Fintype.piFinset_univ, mul_sum, sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun σ _ => ?_
  simp only [submatrix_apply, id, Finset.prod_mul_distrib, mul_assoc]
end MatrixTree
