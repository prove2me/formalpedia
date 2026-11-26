-- Prove2me | solution 1 for MohP3.rho_k_ffK
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:08:46.647877+00:00
-- url     : https://prove2.me/submissions/cb97e787-0288-47a9-a3c0-3584dd16e489

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
theorem _root_.solution (j : Fin 4) : rho_k k (ffK k j) = 0 := by
  fin_cases j
  · show rho_k k (Gen.f1 (xk k) (yk k) (zk k)) = 0
    simp only [Gen.f1, map_add, map_sub, map_mul, map_pow, map_ofNat, rho_k_xk, rho_k_yk, rho_k_zk]
    ring
  · show rho_k k (Gen.f2 (xk k) (yk k) (zk k)) = 0
    simp only [Gen.f2, map_add, map_sub, map_mul, map_pow, map_ofNat, rho_k_xk, rho_k_yk, rho_k_zk]
    ring
  · show rho_k k (Gen.f3 (xk k) (yk k) (zk k)) = 0
    simp only [Gen.f3, map_add, map_sub, map_mul, map_pow, map_ofNat, rho_k_xk, rho_k_yk, rho_k_zk]
    ring
  · show rho_k k (Gen.f4 (xk k) (yk k) (zk k)) = 0
    simp only [Gen.f4, map_add, map_sub, map_mul, map_pow, map_ofNat, rho_k_xk, rho_k_yk, rho_k_zk]
    ring
end MohP3
