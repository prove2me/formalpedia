-- Prove2me | solution 1 for MohP3.f4_notMem_Psurf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:33:18.978734+00:00
-- url     : https://prove2.me/submissions/63a694f7-0051-4bb9-b178-7eb9e99a50e2

module
public import Definitions.Def_MohP3_Global
public import Definitions.Def_MohP3_Ara
public import Definitions.Def_MohP3_Height
public import Theorems.Thm_MohP3_sigma_x
public import Theorems.Thm_MohP3_sigma_y
public import Theorems.Thm_MohP3_sigma_z
public import Theorems.Thm_MohP3_mem_Psurf_iff
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
attribute [local simp] MohP3.sigma_z

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3
namespace MohP3
theorem _root_.solution : f4 ∉ Psurf := by
  intro h
  rw [mem_Psurf_iff] at h
  have h2 : (MvPolynomial.eval ![(1 : ℚ), 1]) (sigma f4) = 0 := by rw [h, map_zero]
  rw [f4] at h2
  simp only [map_sub, map_add, map_mul, map_pow, sigma_x, sigma_y, sigma_z, map_ofNat,
    eval_X] at h2
  norm_num at h2
end MohP3
