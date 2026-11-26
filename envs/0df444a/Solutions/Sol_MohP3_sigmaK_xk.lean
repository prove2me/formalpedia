-- Prove2me | solution 1 for MohP3.sigmaK_xk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:08:41.969731+00:00
-- url     : https://prove2.me/submissions/b3824d2d-f00c-4b3d-a4f9-d1abb3be22ff

module
public import Definitions.Def_MohP3_GlobalK
public import Definitions.Def_MohP3_Ara
public import Definitions.Def_MohP3_HeightK
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



set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3
variable (k : Type*) [Field k] [CharZero k]
omit [CharZero k]
namespace MohP3
theorem _root_.solution : sigmaK k (xk k) = X 0 := by simp [sigmaK, xk]
end MohP3
