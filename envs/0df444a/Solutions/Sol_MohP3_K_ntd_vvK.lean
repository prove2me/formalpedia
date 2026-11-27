-- Prove2me | solution 1 for MohP3.K.ntd_vvK
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:26:33.170683+00:00
-- url     : https://prove2.me/submissions/0d2979ca-c3f3-4ab7-ac3b-855c7502a5cd

module
public import Mathlib
public import Definitions.Def_MohP3_IndependenceK
public import Theorems.Thm_MohP3_K_ntd_X_pow_mul

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Polynomial
open MohP3 MohP3.K
variable (k : Type*) [Field k]
variable {k}
variable (k) [CharZero k]
namespace MohP3.K
theorem _root_.solution (i : Fin 8) : (vvK k i).natTrailingDegree = ooK i := by
  fin_cases i
  · simp [vvK, ooK]
  · simpa [vvK, ooK] using ntd_X_pow_mul 6 (1 + X ^ 25 : Polynomial k) (by simp [coeff_X_pow])
  · simp [vvK, ooK, natTrailingDegree_X_pow]
  · simpa [vvK, ooK] using
      ntd_X_pow_mul 12 (1 + 2 * X ^ 25 + X ^ 50 : Polynomial k) (by simp [coeff_X_pow])
  · simp [vvK, ooK, natTrailingDegree_X_pow]
  · simpa [vvK, ooK] using
      ntd_X_pow_mul 43 (3 + 3 * X ^ 25 + X ^ 50 : Polynomial k) (by simp [coeff_X_pow])
  · simpa [vvK, ooK] using
      ntd_X_pow_mul 45 (-2 - X ^ 25 : Polynomial k) (by simp [coeff_X_pow])
  · simp [vvK, ooK, natTrailingDegree_X_pow]
end MohP3.K
