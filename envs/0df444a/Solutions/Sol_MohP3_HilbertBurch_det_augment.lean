-- Prove2me | solution 1 for MohP3.HilbertBurch.det_augment
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:36:47.832456+00:00
-- url     : https://prove2.me/submissions/2ce1e9e7-6576-4ebf-8bf4-122a276c0e92

module
public import Definitions.Def_MohP3_Generic
public import Mathlib
public import Definitions.Def_MohP3_HilbertBurch
public import Theorems.Thm_MohP3_HilbertBurch_rowMap_apply
public import Theorems.Thm_MohP3_HilbertBurch_augment_submatrix_succ
attribute [local simp] MohP3.HilbertBurch.rowMap_apply

set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open MohP3 MohP3.HilbertBurch
open Matrix
variable {S : Type*} [CommRing S]
namespace MohP3.HilbertBurch
theorem _root_.solution (a : Fin 4 → S) (Φ : Matrix (Fin 4) (Fin 3) S) :
    (augment a Φ).det = ∑ i : Fin 4, (-1) ^ (i : ℕ) * a i * maximalMinor Φ i := by
  rw [Matrix.det_succ_column_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [augment_submatrix_succ]
  simp [augment, maximalMinor]
end MohP3.HilbertBurch
