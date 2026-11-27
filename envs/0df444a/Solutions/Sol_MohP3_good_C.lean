-- Prove2me | solution 1 for MohP3.good_C
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:16:27.63367+00:00
-- url     : https://prove2.me/submissions/0fad4d68-51ea-4e19-9b1b-a1f63dde40a7

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
theorem _root_.solution (a : ℚ) : Good (MvPolynomial.C a) := by
  refine ⟨1, one_ne_zero, ![Polynomial.C a, 0, 0, 0, 0, 0, 0, 0], ?_⟩
  have h : ((1:ℕ) : R) * MvPolynomial.C a
      - ∑ i, iota ((![Polynomial.C a, 0, 0, 0, 0, 0, 0, 0] : Fin 8 → Polynomial ℚ) i) * hh i
      = 0 := by
    simp [Fin.sum_univ_eight, hh]
  rw [h]
  exact Ideal.zero_mem P
end MohP3
