-- Prove2me | solution 1 for MohP3.good_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:16:44.209907+00:00
-- url     : https://prove2.me/submissions/18996f5f-806e-42c4-8eb3-84b4d31c31fa

module
public import Definitions.Def_MohP3_Closure
public import Definitions.Def_MohP3_Independence
public import Definitions.Def_MohP3_Kernel
public import Theorems.Thm_MohP3_iota_C
public import Theorems.Thm_MohP3_iota_X
public import Theorems.Thm_MohP3_iota_ofNat
public import Theorems.Thm_MohP3_rho_C
public import Theorems.Thm_MohP3_rho_x
public import Theorems.Thm_MohP3_rho_y
public import Theorems.Thm_MohP3_rho_z
attribute [local simp] MohP3.iota_C
attribute [local simp] MohP3.iota_X
attribute [local simp] MohP3.iota_ofNat
attribute [local simp] MohP3.rho_C
attribute [local simp] MohP3.rho_x
attribute [local simp] MohP3.rho_y
attribute [local simp] MohP3.rho_z



set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3
namespace MohP3
theorem _root_.solution {g₁ g₂ : R} (h₁ : Good g₁) (h₂ : Good g₂) : Good (g₁ + g₂) := by
  obtain ⟨n₁, hn₁, p, hp⟩ := h₁
  obtain ⟨n₂, hn₂, q, hq⟩ := h₂
  refine ⟨n₁*n₂, mul_ne_zero hn₁ hn₂,
    fun i => (n₂ : Polynomial ℚ) * p i + (n₁ : Polynomial ℚ) * q i, ?_⟩
  have key : ((n₁*n₂ : ℕ) : R) * (g₁ + g₂)
      - ∑ i, iota ((n₂ : Polynomial ℚ) * p i + (n₁ : Polynomial ℚ) * q i) * hh i
      = (n₂ : R) * ((n₁ : R) * g₁ - ∑ i, iota (p i) * hh i)
        + (n₁ : R) * ((n₂ : R) * g₂ - ∑ i, iota (q i) * hh i) := by
    push_cast
    simp only [map_add, map_mul, map_natCast, Fin.sum_univ_eight]
    ring
  rw [key]
  exact P.add_mem (Ideal.mul_mem_left _ _ hp) (Ideal.mul_mem_left _ _ hq)
end MohP3
