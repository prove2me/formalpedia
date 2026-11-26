-- Prove2me | solution 1 for MohP3.rho_C
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:44:56.385249+00:00
-- url     : https://prove2.me/submissions/33c2c8bc-2bc7-48b4-8f8a-98340223561d

module
public import Mathlib
public import Definitions.Def_MohP3_Defs

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3
namespace MohP3
theorem _root_.solution (a : ℚ) : rho (C a) = Polynomial.C a := by
  simp [rho]
end MohP3
