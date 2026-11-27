-- Prove2me | solution 1 for MohP3.HilbertBurch.cofactor_column
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:37:06.722807+00:00
-- url     : https://prove2.me/submissions/501bb55d-cc25-40c0-bcee-93a74fb7ca16

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
theorem _root_.solution (a : Fin 4 → S) (Φ : Matrix (Fin 4) (Fin 3) S) (j : Fin 4) :
    ∃ w : Fin 3 → S, ∀ r : Fin 4,
      a r * ((-1) ^ (j : ℕ) * maximalMinor Φ j) + (Φ *ᵥ w) r =
        if r = j then (augment a Φ).det else 0 := by
  refine ⟨fun c => (augment a Φ).adjugate c.succ j, fun r => ?_⟩
  have h := congrFun (congrFun (Matrix.mul_adjugate (augment a Φ)) r) j
  rw [Matrix.mul_apply, Fin.sum_univ_succ] at h
  have h0 : (augment a Φ).adjugate 0 j = (-1) ^ (j : ℕ) * maximalMinor Φ j := by
    rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
    simp only [Fin.val_zero, add_zero, Fin.succAbove_zero]
    rw [augment_submatrix_succ]
    rfl
  rw [h0] at h
  simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one,
    mul_zero] at h
  rw [← h]
  simp [augment, Matrix.mulVec, dotProduct]
end MohP3.HilbertBurch
