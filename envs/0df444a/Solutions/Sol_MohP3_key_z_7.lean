-- Prove2me | solution 1 for MohP3.key_z_7
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:16:18.41781+00:00
-- url     : https://prove2.me/submissions/3be4b501-0e40-4778-add9-4f2b9ef01045

module
public import Definitions.Def_MohP3_Certificate
public import Definitions.Def_MohP3_Closure
public import Theorems.Thm_MohP3_iota_X
public import Theorems.Thm_MohP3_iota_C
public import Theorems.Thm_MohP3_iota_ofNat
public import Theorems.Thm_MohP3_Gen_mem_P_of_eq
public import Theorems.Thm_MohP3_mem_P_of_eq
public import Theorems.Thm_MohP3_rho_C
public import Theorems.Thm_MohP3_rho_x
public import Theorems.Thm_MohP3_rho_y
public import Theorems.Thm_MohP3_rho_z
attribute [local simp] MohP3.rho_C
attribute [local simp] MohP3.rho_x
attribute [local simp] MohP3.rho_y
attribute [local simp] MohP3.rho_z


attribute [local simp] MohP3.iota_X
attribute [local simp] MohP3.iota_C
attribute [local simp] MohP3.iota_ofNat

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3
namespace MohP3
theorem _root_.solution : (18 : R) * (z * hh 7) - ∑ j, iota (QZ 7 j) * hh j ∈ P :=
  mem_P_of_eq (c1 := -6*y^6*z + 6*y) (c2 := 6*x*y^5*z - 6*x) (c3 := 0) (c4 := 18*y^4*z^2) (by
    simp only [hh, QZ, Fin.sum_univ_eight, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, iota_X, iota_ofNat, map_mul, map_pow, map_zero,
      f1, f2, f3, f4]
    ring)
end MohP3
