-- Prove2me | solution 1 for MohP3.sigma_y
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:03:44.81303+00:00
-- url     : https://prove2.me/submissions/fc873578-edab-48e2-af74-54b2f3dd74fa

module
public import Definitions.Def_MohP3_Global
public import Definitions.Def_MohP3_Ara
public import Definitions.Def_MohP3_Height
public import Theorems.Thm_MohP3_sigma_x
public import Theorems.Thm_MohP3_iota_C
public import Theorems.Thm_MohP3_iota_X
public import Theorems.Thm_MohP3_iota_ofNat
public import Theorems.Thm_MohP3_rho_C
public import Theorems.Thm_MohP3_rho_x
public import Theorems.Thm_MohP3_rho_y
public import Theorems.Thm_MohP3_rho_z
attribute [local simp] MohP3.iota_C
attribute [local simp] MohP3.iota_X
attribute [local simp] MohP3.iota_ofNat
attribute [local simp] MohP3.rho_C
attribute [local simp] MohP3.rho_x
attribute [local simp] MohP3.rho_y
attribute [local simp] MohP3.rho_z


attribute [local simp] MohP3.sigma_x

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3
namespace MohP3
theorem _root_.solution : sigma y = (X 1 : Rsurf)^4 := by
  simp [sigma, y, Matrix.cons_val_one]
end MohP3
