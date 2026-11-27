-- Prove2me | solution 1 for MohP3.kernel_rho
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:21:24.391558+00:00
-- url     : https://prove2.me/submissions/461f679c-b79d-4085-b5ae-ca7b40d2d9bb

module
public import Definitions.Def_MohP3_Closure
public import Definitions.Def_MohP3_Independence
public import Definitions.Def_MohP3_Kernel
public import Theorems.Thm_MohP3_rho_hh
public import Theorems.Thm_MohP3_rho_iota
public import Theorems.Thm_MohP3_good_all
public import Theorems.Thm_MohP3_P_le_ker
public import Theorems.Thm_MohP3_Gen_mem_of_nsmul_mem
public import Theorems.Thm_MohP3_indep
public import Theorems.Thm_MohP3_iota_C
public import Theorems.Thm_MohP3_iota_X
public import Theorems.Thm_MohP3_iota_ofNat
public import Theorems.Thm_MohP3_mem_of_nsmul_mem
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
theorem _root_.solution : RingHom.ker rho = P := by
  refine le_antisymm ?_ P_le_ker
  intro g hg
  obtain ⟨n, hn, p, hp⟩ := good_all g
  have hng : (n : R) * g ∈ RingHom.ker rho := Ideal.mul_mem_left _ _ hg
  have hsum_ker : (∑ i, iota (p i) * hh i) ∈ RingHom.ker rho := by
    simpa using sub_mem hng (P_le_ker hp)
  have h2 : ∑ i, (p i).comp (Polynomial.X^8) * vv i = 0 := by
    have h := RingHom.mem_ker.mp hsum_ker
    rw [map_sum] at h
    simpa [map_mul, rho_iota, rho_hh] using h
  have h3 := indep p h2
  have hzero : ∑ i, iota (p i) * hh i = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    simp [h3 i]
  rw [hzero, sub_zero] at hp
  exact mem_of_nsmul_mem hn hp
end MohP3
