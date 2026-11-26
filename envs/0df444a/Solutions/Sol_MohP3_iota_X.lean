-- Prove2me | solution 1 for MohP3.iota_X
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:53:40.670694+00:00
-- url     : https://prove2.me/submissions/4f5b5843-5087-4c81-bdf9-bb7bbe7dc222

module
public import Definitions.Def_MohP3_Certificate
public import Definitions.Def_MohP3_Closure
public import Theorems.Thm_MohP3_rho_C
public import Theorems.Thm_MohP3_rho_x
public import Theorems.Thm_MohP3_rho_y
public import Theorems.Thm_MohP3_rho_z
attribute [local simp] MohP3.rho_C
attribute [local simp] MohP3.rho_x
attribute [local simp] MohP3.rho_y
attribute [local simp] MohP3.rho_z



set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3
namespace MohP3
theorem _root_.solution : iota Polynomial.X = y := by simp [iota]
end MohP3
