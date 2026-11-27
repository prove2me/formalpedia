-- Prove2me | solution 1 for MohP3.good_mul_y
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:16:54.284409+00:00
-- url     : https://prove2.me/submissions/88fc9c68-0b17-4b12-91ea-a095fbdb8e99

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
theorem _root_.solution {g : R} (h : Good g) : Good (y * g) := by
  obtain ⟨n, hn, p, hp⟩ := h
  refine ⟨n, hn, fun i => Polynomial.X * p i, ?_⟩
  have key : (n : R) * (y * g) - ∑ i, iota (Polynomial.X * p i) * hh i
      = y * ((n : R) * g - ∑ i, iota (p i) * hh i) := by
    simp only [map_mul, iota_X, Fin.sum_univ_eight]
    ring
  rw [key]
  exact Ideal.mul_mem_left _ _ hp
end MohP3
