-- Prove2me | solution 1 for MohP3.f3_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:51:37.573792+00:00
-- url     : https://prove2.me/submissions/16af096c-4415-4c8b-8d65-91bfd85c57f1

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
theorem _root_.solution : f3 ∈ P := Ideal.subset_span (by simp)
end MohP3
