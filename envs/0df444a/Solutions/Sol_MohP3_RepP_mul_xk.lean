-- Prove2me | solution 1 for MohP3.RepP_mul_xk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:32:04.080433+00:00
-- url     : https://prove2.me/submissions/21fee30f-a1c8-4f29-a810-676f8e6f7a91

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
public import Theorems.Thm_MohP3_key_x_divK
public import Theorems.Thm_MohP3_iotaK_qxPoly
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
namespace MohP3
theorem _root_.solution {g : Rk k} (h : RepP k g) : RepP k (xk k * g) := by
  obtain ⟨p, c, hp⟩ := h
  refine ⟨fun j => Polynomial.C ((18 : k)⁻¹) * ∑ i, p i * qxPoly k i j,
    fun j => xk k * c j + MvPolynomial.C ((18 : k)⁻¹) *
      ∑ i, iotaK k (p i) * Gen.wxA (xk k) (yk k) (zk k) i j, ?_⟩
  have hp' : ∀ j : Fin 8, iotaK k (Polynomial.C ((18 : k)⁻¹) * ∑ i, p i * qxPoly k i j) =
      MvPolynomial.C ((18 : k)⁻¹) * ∑ i, iotaK k (p i) * Gen.qxA (yk k) i j := by
    intro j
    rw [map_mul, iotaK_C, map_sum]
    simp only [map_mul, iotaK_qxPoly]
  simp only [hp']
  have e0 := key_x_divK k 0
  have e1 := key_x_divK k 1
  have e2 := key_x_divK k 2
  have e3 := key_x_divK k 3
  have e4 := key_x_divK k 4
  have e5 := key_x_divK k 5
  have e6 := key_x_divK k 6
  have e7 := key_x_divK k 7
  simp only [Fin.sum_univ_eight, Fin.sum_univ_four] at hp e0 e1 e2 e3 e4 e5 e6 e7 ⊢
  linear_combination (xk k) * hp + iotaK k (p 0) * e0 + iotaK k (p 1) * e1 +
    iotaK k (p 2) * e2 + iotaK k (p 3) * e3 + iotaK k (p 4) * e4 + iotaK k (p 5) * e5 +
    iotaK k (p 6) * e6 + iotaK k (p 7) * e7
end MohP3
