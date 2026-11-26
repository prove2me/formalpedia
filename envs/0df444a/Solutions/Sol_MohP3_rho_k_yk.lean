-- Prove2me | solution 1 for MohP3.rho_k_yk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:04:13.020925+00:00
-- url     : https://prove2.me/submissions/777991e1-5b30-4297-98cd-2df62a2f3722

module
public import Definitions.Def_MohP3_GenClosure
public import Definitions.Def_MohP3_IndependenceK
public import Definitions.Def_MohP3_GlobalK
public import Theorems.Thm_MohP3_rho_k_C
public import Theorems.Thm_MohP3_rho_k_xk
attribute [local simp] MohP3.rho_k_C
attribute [local simp] MohP3.rho_k_xk

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3
variable (k : Type*) [Field k] [CharZero k]
omit [CharZero k]
namespace MohP3
theorem _root_.solution : rho_k k (yk k) = Polynomial.X ^ 8 := by simp [rho_k, yk]
end MohP3
