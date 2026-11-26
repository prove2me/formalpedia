-- Prove2me | solution 1 for MohP3.rho_k_zk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:05:13.939824+00:00
-- url     : https://prove2.me/submissions/6ba626d1-12b6-4054-8506-583c2756b1ad

module
public import Definitions.Def_MohP3_GenClosure
public import Definitions.Def_MohP3_IndependenceK
public import Definitions.Def_MohP3_GlobalK
public import Theorems.Thm_MohP3_rho_k_C
public import Theorems.Thm_MohP3_rho_k_xk
public import Theorems.Thm_MohP3_rho_k_yk
attribute [local simp] MohP3.rho_k_C
attribute [local simp] MohP3.rho_k_xk
attribute [local simp] MohP3.rho_k_yk

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3
variable (k : Type*) [Field k] [CharZero k]
omit [CharZero k]
namespace MohP3
theorem _root_.solution : rho_k k (zk k) = Polynomial.X ^ 10 := by simp [rho_k, zk]
end MohP3
