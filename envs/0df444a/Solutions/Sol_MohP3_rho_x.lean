-- Prove2me | solution 1 for MohP3.rho_x
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:45:57.665648+00:00
-- url     : https://prove2.me/submissions/c8e0528c-806c-4e43-9b38-ce570cad5dfb

module
public import Mathlib
public import Definitions.Def_MohP3_Defs
public import Theorems.Thm_MohP3_rho_C
attribute [local simp] MohP3.rho_C

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3
namespace MohP3
theorem _root_.solution : rho x = Polynomial.X^6 + Polynomial.X^31 := by
  simp [rho, x]
end MohP3
