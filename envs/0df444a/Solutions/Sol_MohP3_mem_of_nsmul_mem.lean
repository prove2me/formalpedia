-- Prove2me | solution 1 for MohP3.mem_of_nsmul_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:05:27.533146+00:00
-- url     : https://prove2.me/submissions/e00a4993-4e7b-4276-8c82-d3e10059ac21

module
public import Mathlib
public import Definitions.Def_MohP3_Defs
public import Theorems.Thm_MohP3_rho_C
public import Theorems.Thm_MohP3_rho_x
public import Theorems.Thm_MohP3_rho_y
public import Theorems.Thm_MohP3_rho_z
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
theorem _root_.solution {I : Ideal R} {n : ℕ} (hn : n ≠ 0) {g : R}
    (h : (n : R) * g ∈ I) : g ∈ I := by
  have hq : ((n : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have h2 := Ideal.mul_mem_left I (C ((n : ℚ))⁻¹) h
  rwa [← mul_assoc, show ((n : R)) = C ((n : ℚ)) by simp, ← C_mul,
    inv_mul_cancel₀ hq, C_1, one_mul] at h2
end MohP3
