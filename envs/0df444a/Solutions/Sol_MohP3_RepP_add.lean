-- Prove2me | solution 1 for MohP3.RepP_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:27:48.196317+00:00
-- url     : https://prove2.me/submissions/56cdf261-115b-483c-8d9c-0a98a76b9f25

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
theorem _root_.solution {g₁ g₂ : Rk k} (h₁ : RepP k g₁) (h₂ : RepP k g₂) : RepP k (g₁ + g₂) := by
  obtain ⟨p, c, hp⟩ := h₁
  obtain ⟨p', c', hp'⟩ := h₂
  refine ⟨p + p', c + c', ?_⟩
  rw [hp, hp']
  simp only [Pi.add_apply, map_add, Fin.sum_univ_eight, Fin.sum_univ_four, add_mul]
  ring
end MohP3
