-- Prove2me | solution 1 for MohP3.PsurfK_ne_bot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:35:38.098445+00:00
-- url     : https://prove2.me/submissions/5a165756-7d0b-4ceb-be1c-1f99048a7835

module
public import Definitions.Def_MohP3_GlobalK
public import Definitions.Def_MohP3_Ara
public import Definitions.Def_MohP3_HeightK
public import Theorems.Thm_MohP3_sigmaK_xk
public import Theorems.Thm_MohP3_sigmaK_yk
public import Theorems.Thm_MohP3_sigmaK_zk
public import Theorems.Thm_MohP3_mem_PsurfK_iff
public import Theorems.Thm_MohP3_iotaK_C
public import Theorems.Thm_MohP3_iotaK_X
public import Theorems.Thm_MohP3_rho_k_C
public import Theorems.Thm_MohP3_rho_k_xk
public import Theorems.Thm_MohP3_rho_k_yk
public import Theorems.Thm_MohP3_rho_k_zk
attribute [local simp] MohP3.iotaK_C
attribute [local simp] MohP3.iotaK_X
attribute [local simp] MohP3.rho_k_C
attribute [local simp] MohP3.rho_k_xk
attribute [local simp] MohP3.rho_k_yk
attribute [local simp] MohP3.rho_k_zk


attribute [local simp] MohP3.sigmaK_xk
attribute [local simp] MohP3.sigmaK_yk
attribute [local simp] MohP3.sigmaK_zk

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3
variable (k : Type*) [Field k] [CharZero k]
omit [CharZero k]
namespace MohP3
theorem _root_.solution : PsurfK k ≠ ⊥ := by
  have hmem : (yk k)^5 - (zk k)^4 ∈ PsurfK k := by
    rw [mem_PsurfK_iff]
    simp only [map_sub, map_pow, sigmaK_yk, sigmaK_zk]
    ring
  have hne : ((yk k)^5 - (zk k)^4 : Rk k) ≠ 0 := by
    intro h
    have h2 := congrArg (MvPolynomial.eval ![0, 1, 0]) h
    simp [yk, zk] at h2
  intro h
  rw [h, Ideal.mem_bot] at hmem
  exact hne hmem
end MohP3
