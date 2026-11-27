-- Prove2me | solution 1 for MohP3.Psurf_le_P
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:33:26.29581+00:00
-- url     : https://prove2.me/submissions/2faa2f7a-55f1-4150-8497-0122772b6ffa

module
public import Definitions.Def_MohP3_Global
public import Definitions.Def_MohP3_Ara
public import Definitions.Def_MohP3_Height
public import Theorems.Thm_MohP3_rho_eq_tau_comp_sigma
public import Theorems.Thm_MohP3_mem_Psurf_iff
public import Theorems.Thm_MohP3_kernel_rho


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3
namespace MohP3
theorem _root_.solution : Psurf ≤ P := by
  rw [← kernel_rho]
  intro g hg
  rw [mem_Psurf_iff] at hg
  rw [RingHom.mem_ker, rho_eq_tau_comp_sigma, RingHom.comp_apply, hg, map_zero]
end MohP3
