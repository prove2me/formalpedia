-- Prove2me | solution 1 for MohP3.sigmaK_yk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:09:31.26898+00:00
-- url     : https://prove2.me/submissions/3ccaf50a-7972-4da2-86b9-671f935e5fd0

module
public import Definitions.Def_MohP3_GlobalK
public import Definitions.Def_MohP3_Ara
public import Definitions.Def_MohP3_HeightK
public import Theorems.Thm_MohP3_sigmaK_xk
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

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3
variable (k : Type*) [Field k] [CharZero k]
omit [CharZero k]
namespace MohP3
theorem _root_.solution : sigmaK k (yk k) = (X 1 : MvPolynomial (Fin 2) k)^4 := by
  simp [sigmaK, yk, Matrix.cons_val_one]
end MohP3
