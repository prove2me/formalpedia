-- Prove2me | solution 1 for MohP3.P_le_ker
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:18:54.823806+00:00
-- url     : https://prove2.me/submissions/7f7bd8c6-e0b6-472d-bda4-8c2952bba805

module
public import Definitions.Def_MohP3_Closure
public import Definitions.Def_MohP3_Independence
public import Definitions.Def_MohP3_Kernel
public import Theorems.Thm_MohP3_rho_f1
public import Theorems.Thm_MohP3_rho_f2
public import Theorems.Thm_MohP3_rho_f3
public import Theorems.Thm_MohP3_rho_f4
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
theorem _root_.solution : P ≤ RingHom.ker rho := by
  rw [P, Ideal.span_le]
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact RingHom.mem_ker.mpr rho_f1
  · exact RingHom.mem_ker.mpr rho_f2
  · exact RingHom.mem_ker.mpr rho_f3
  · exact RingHom.mem_ker.mpr rho_f4
end MohP3
