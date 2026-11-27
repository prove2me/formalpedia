-- Prove2me | solution 1 for MohP3.sigmaK_zk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:11:30.147256+00:00
-- url     : https://prove2.me/submissions/e7adca0f-c08f-4776-82ba-52ad31092d4e

module
public import Definitions.Def_MohP3_GlobalK
public import Definitions.Def_MohP3_Ara
public import Definitions.Def_MohP3_HeightK
public import Theorems.Thm_MohP3_sigmaK_xk
public import Theorems.Thm_MohP3_sigmaK_yk
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

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3
variable (k : Type*) [Field k] [CharZero k]
omit [CharZero k]
namespace MohP3
theorem _root_.solution : sigmaK k (zk k) = (X 1 : MvPolynomial (Fin 2) k)^5 := by
  simp [sigmaK, zk]
end MohP3
