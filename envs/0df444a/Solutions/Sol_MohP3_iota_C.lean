-- Prove2me | solution 1 for MohP3.iota_C
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:55:33.726596+00:00
-- url     : https://prove2.me/submissions/adb0e75e-75b6-4682-94b6-1e594da25986

module
public import Definitions.Def_MohP3_Certificate
public import Definitions.Def_MohP3_Closure
public import Theorems.Thm_MohP3_iota_X
public import Theorems.Thm_MohP3_rho_C
public import Theorems.Thm_MohP3_rho_x
public import Theorems.Thm_MohP3_rho_y
public import Theorems.Thm_MohP3_rho_z
attribute [local simp] MohP3.rho_C
attribute [local simp] MohP3.rho_x
attribute [local simp] MohP3.rho_y
attribute [local simp] MohP3.rho_z


attribute [local simp] MohP3.iota_X

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3
namespace MohP3
theorem _root_.solution (a : ℚ) : iota (Polynomial.C a) = MvPolynomial.C a := by simp [iota]
end MohP3
