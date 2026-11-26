-- Prove2me | solution 1 for MohP3.H2_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:51:40.261894+00:00
-- url     : https://prove2.me/submissions/531a218c-b80b-4cdf-8637-9400c9b7e403

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
theorem _root_.solution : H2 ∈ Q := Ideal.subset_span (by simp)
end MohP3
