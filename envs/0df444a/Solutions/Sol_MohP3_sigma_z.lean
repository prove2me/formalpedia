-- Prove2me | solution 1 for MohP3.sigma_z
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:05:34.646793+00:00
-- url     : https://prove2.me/submissions/cb97b1ef-dd8c-4045-bc74-1b915223874a

module
public import Definitions.Def_MohP3_Global
public import Definitions.Def_MohP3_Ara
public import Definitions.Def_MohP3_Height
public import Theorems.Thm_MohP3_sigma_x
public import Theorems.Thm_MohP3_sigma_y
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
attribute [local simp] MohP3.sigma_y

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3
namespace MohP3
theorem _root_.solution : sigma z = (X 1 : Rsurf)^5 := by
  simp [sigma, z]
end MohP3
