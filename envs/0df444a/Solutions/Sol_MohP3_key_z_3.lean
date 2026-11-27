-- Prove2me | solution 1 for MohP3.key_z_3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:15:32.489592+00:00
-- url     : https://prove2.me/submissions/884294a2-dbbe-452c-9ccb-eb3a986c7ce5

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
theorem _root_.solution : (18 : R) * (z * hh 3) - ∑ j, iota (QZ 3 j) * hh j ∈ P :=
  mem_P_of_eq (c1 := 0) (c2 := 0) (c3 := 0) (c4 := 0) (by
    simp only [hh, QZ, Fin.sum_univ_eight, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, iota_X, iota_ofNat, map_mul, map_pow, map_zero,
      f1, f2, f3, f4]
    ring)
end MohP3
