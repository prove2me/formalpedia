-- Prove2me | solution 1 for MohP3.rho_iota
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:16:24.595922+00:00
-- url     : https://prove2.me/submissions/35b9bf60-5e83-4bf9-8c4e-e20d0bd837aa

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
theorem _root_.solution (p : Polynomial ℚ) : rho (iota p) = p.comp (Polynomial.X^8) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial k a =>
      rw [Polynomial.monomial_comp, ← pow_mul,
        show iota ((Polynomial.monomial k) a) = MvPolynomial.C a * y ^ k by
          simp [iota, Polynomial.eval₂_monomial],
        map_mul, map_pow, rho_y, rho_C, ← pow_mul]
end MohP3
