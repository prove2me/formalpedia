-- Prove2me | solution 1 for MohP3.H1_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:51:39.335817+00:00
-- url     : https://prove2.me/submissions/f0b4e3e7-7238-4c7c-a780-5708e7715609

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
theorem _root_.solution : H1 ∈ Q := Ideal.subset_span (by simp)
end MohP3
