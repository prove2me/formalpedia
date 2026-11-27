-- Prove2me | solution 1 for MohP3.rho_k_iotaK
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:26:49.247124+00:00
-- url     : https://prove2.me/submissions/438f040d-706e-475f-a3df-2f9ce09c417e

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
theorem _root_.solution (p : Polynomial k) : rho_k k (iotaK k p) = p.comp (Polynomial.X ^ 8) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial m a =>
      rw [Polynomial.monomial_comp, ← pow_mul,
        show iotaK k ((Polynomial.monomial m) a) = MvPolynomial.C a * yk k ^ m by
          simp [iotaK, Polynomial.eval₂_monomial],
        map_mul, map_pow, rho_k_yk, rho_k_C, ← pow_mul]
end MohP3
