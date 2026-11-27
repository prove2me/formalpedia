-- Prove2me | solution 1 for MohP3.rho_k_hhK
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:26:46.512248+00:00
-- url     : https://prove2.me/submissions/93029de5-757a-4d1e-b70e-0c4801f5592f

module
public import Definitions.Def_MohP3_GenClosure
public import Definitions.Def_MohP3_IndependenceK
public import Definitions.Def_MohP3_GlobalK
public import Theorems.Thm_MohP3_rho_k_C
public import Theorems.Thm_MohP3_rho_k_xk
public import Theorems.Thm_MohP3_rho_k_yk
public import Theorems.Thm_MohP3_rho_k_zk
public import Theorems.Thm_MohP3_iotaK_X
public import Theorems.Thm_MohP3_iotaK_C
attribute [local simp] MohP3.rho_k_C
attribute [local simp] MohP3.rho_k_xk
attribute [local simp] MohP3.rho_k_yk
attribute [local simp] MohP3.rho_k_zk
attribute [local simp] MohP3.iotaK_X
attribute [local simp] MohP3.iotaK_C

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3
variable (k : Type*) [Field k] [CharZero k]
omit [CharZero k]
namespace MohP3
theorem _root_.solution (i : Fin 8) : rho_k k (hhK k i) = K.vvK k i := by
  fin_cases i <;> simp [hhK, Gen.hh, K.vvK, xk, yk, zk, rho_k] <;> ring
end MohP3
