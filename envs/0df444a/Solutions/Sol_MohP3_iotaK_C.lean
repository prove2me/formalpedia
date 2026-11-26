-- Prove2me | solution 1 for MohP3.iotaK_C
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:07:54.454854+00:00
-- url     : https://prove2.me/submissions/c601821f-41a5-482a-a808-6e6d7cf97e4c

module
public import Definitions.Def_MohP3_GenClosure
public import Definitions.Def_MohP3_IndependenceK
public import Definitions.Def_MohP3_GlobalK
public import Theorems.Thm_MohP3_rho_k_C
public import Theorems.Thm_MohP3_rho_k_xk
public import Theorems.Thm_MohP3_rho_k_yk
public import Theorems.Thm_MohP3_rho_k_zk
public import Theorems.Thm_MohP3_iotaK_X
attribute [local simp] MohP3.rho_k_C
attribute [local simp] MohP3.rho_k_xk
attribute [local simp] MohP3.rho_k_yk
attribute [local simp] MohP3.rho_k_zk
attribute [local simp] MohP3.iotaK_X

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3
variable (k : Type*) [Field k] [CharZero k]
omit [CharZero k]
namespace MohP3
theorem _root_.solution (a : k) : iotaK k (Polynomial.C a) = MvPolynomial.C a := by simp [iotaK]
end MohP3
