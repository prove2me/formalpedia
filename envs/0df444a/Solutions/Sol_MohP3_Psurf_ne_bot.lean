-- Prove2me | solution 1 for MohP3.Psurf_ne_bot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:32:22.43907+00:00
-- url     : https://prove2.me/submissions/c4f2e385-9705-4593-ab61-a9be93a7444c

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
theorem _root_.solution : Psurf ≠ ⊥ := by
  have hmem : y^5 - z^4 ∈ Psurf := by
    rw [mem_Psurf_iff]
    simp only [map_sub, map_pow, sigma_y, sigma_z]
    ring
  have hne : (y^5 - z^4 : R) ≠ 0 := by
    intro h
    have := congrArg (MvPolynomial.eval ![0, 1, 0]) h
    simp [y, z] at this
  intro h
  rw [h, Ideal.mem_bot] at hmem
  exact hne hmem
end MohP3
