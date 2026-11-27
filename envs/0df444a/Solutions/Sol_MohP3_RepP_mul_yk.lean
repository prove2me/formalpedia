-- Prove2me | solution 1 for MohP3.RepP_mul_yk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:27:55.120276+00:00
-- url     : https://prove2.me/submissions/15c2f463-974d-4dbb-bd34-23bb35c5e8e2

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
theorem _root_.solution {g : Rk k} (h : RepP k g) : RepP k (yk k * g) := by
  obtain ⟨p, c, hp⟩ := h
  refine ⟨fun i => Polynomial.X * p i, fun j => yk k * c j, ?_⟩
  rw [hp]
  simp only [map_mul, iotaK_X, Fin.sum_univ_eight, Fin.sum_univ_four]
  ring
end MohP3
