-- Prove2me | solution 1 for MohP3.f4K_notMem_PsurfK
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:35:40.942192+00:00
-- url     : https://prove2.me/submissions/5a7fbbee-da32-4961-aa4f-22fd7a801bd6

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
theorem _root_.solution : Gen.f4 (xk k) (yk k) (zk k) ∉ PsurfK k := by
  intro h
  rw [mem_PsurfK_iff] at h
  have h2 : (MvPolynomial.eval ![(1 : k), 1]) (sigmaK k (Gen.f4 (xk k) (yk k) (zk k))) = 0 := by
    rw [h, map_zero]
  rw [Gen.f4] at h2
  simp only [map_sub, map_add, map_mul, map_pow, sigmaK_xk, sigmaK_yk, sigmaK_zk, map_ofNat,
    eval_X] at h2
  norm_num at h2
end MohP3
