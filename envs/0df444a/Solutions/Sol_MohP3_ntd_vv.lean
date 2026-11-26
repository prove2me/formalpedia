-- Prove2me | solution 1 for MohP3.ntd_vv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:46:20.831238+00:00
-- url     : https://prove2.me/submissions/f4a4741b-5624-4f96-83d9-e56828978044

module
public import Mathlib
public import Definitions.Def_MohP3_Independence
public import Theorems.Thm_MohP3_ntd_X_pow_mul

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Polynomial
open MohP3
namespace MohP3
theorem _root_.solution (i : Fin 8) : (vv i).natTrailingDegree = oo i := by
  fin_cases i
  · simp [vv, oo]
  · simpa [vv, oo] using ntd_X_pow_mul 6 (1+X^25) (by simp [coeff_X_pow])
  · simp [vv, oo, natTrailingDegree_X_pow]
  · simpa [vv, oo] using ntd_X_pow_mul 12 (1+2*X^25+X^50) (by simp [coeff_X_pow])
  · simp [vv, oo, natTrailingDegree_X_pow]
  · simpa [vv, oo] using ntd_X_pow_mul 43 (3+3*X^25+X^50) (by simp [coeff_X_pow])
  · simpa [vv, oo] using ntd_X_pow_mul 45 (-2-X^25) (by simp [coeff_X_pow])
  · simp [vv, oo, natTrailingDegree_X_pow]
end MohP3
