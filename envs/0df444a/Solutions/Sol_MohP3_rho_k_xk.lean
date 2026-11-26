-- Prove2me | solution 1 for MohP3.rho_k_xk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:03:02.379717+00:00
-- url     : https://prove2.me/submissions/beed98e7-174c-4d86-8bf1-d80c78542e58

module
public import Definitions.Def_MohP3_GenClosure
public import Definitions.Def_MohP3_IndependenceK
public import Definitions.Def_MohP3_GlobalK
public import Theorems.Thm_MohP3_rho_k_C
attribute [local simp] MohP3.rho_k_C

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3
variable (k : Type*) [Field k] [CharZero k]
omit [CharZero k]
namespace MohP3
theorem _root_.solution : rho_k k (xk k) = Polynomial.X ^ 6 + Polynomial.X ^ 31 := by
  simp [rho_k, xk]
end MohP3
