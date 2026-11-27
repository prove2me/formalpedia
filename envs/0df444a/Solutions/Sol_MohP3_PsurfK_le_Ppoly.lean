-- Prove2me | solution 1 for MohP3.PsurfK_le_Ppoly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:36:14.65155+00:00
-- url     : https://prove2.me/submissions/5300ad97-6da3-4247-a604-36377d560c26

module
public import Definitions.Def_MohP3_GlobalK
public import Definitions.Def_MohP3_Ara
public import Definitions.Def_MohP3_HeightK
public import Theorems.Thm_MohP3_rho_k_eq_tauK_comp_sigmaK
public import Theorems.Thm_MohP3_mem_PsurfK_iff
public import Theorems.Thm_MohP3_global_kernel_k


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3
variable (k : Type*) [Field k] [CharZero k]
namespace MohP3
theorem _root_.solution : PsurfK k ≤ Ppoly k := by
  rw [← global_kernel_k]
  intro g hg
  rw [mem_PsurfK_iff] at hg
  rw [RingHom.mem_ker, rho_k_eq_tauK_comp_sigmaK, RingHom.comp_apply, hg, map_zero]
end MohP3
