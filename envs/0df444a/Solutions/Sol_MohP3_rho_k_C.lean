-- Prove2me | solution 1 for MohP3.rho_k_C
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:01:59.379391+00:00
-- url     : https://prove2.me/submissions/07821fff-6f9c-4791-984d-fe43ec6996d9

module
public import Definitions.Def_MohP3_GenClosure
public import Definitions.Def_MohP3_IndependenceK
public import Definitions.Def_MohP3_GlobalK

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3
variable (k : Type*) [Field k] [CharZero k]
omit [CharZero k]
namespace MohP3
theorem _root_.solution (a : k) : rho_k k (MvPolynomial.C a) = Polynomial.C a := by simp [rho_k]
end MohP3
