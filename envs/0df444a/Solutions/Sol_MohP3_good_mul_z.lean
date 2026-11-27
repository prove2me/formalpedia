-- Prove2me | solution 1 for MohP3.good_mul_z
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:18:50.311795+00:00
-- url     : https://prove2.me/submissions/3af3770c-31b2-4a12-be5f-cacf3ee192d9

module
public import Definitions.Def_MohP3_Closure
public import Definitions.Def_MohP3_Independence
public import Definitions.Def_MohP3_Kernel
public import Theorems.Thm_MohP3_iota_C
public import Theorems.Thm_MohP3_iota_X
public import Theorems.Thm_MohP3_iota_ofNat
public import Theorems.Thm_MohP3_key_z
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
theorem _root_.solution {g : R} (h : Good g) : Good (z * g) := by
  obtain ⟨n, hn, p, hp⟩ := h
  refine ⟨18*n, by simpa using hn, fun j => ∑ i, p i * QZ i j, ?_⟩
  have key : ((18*n : ℕ) : R) * (z * g) - ∑ j, iota (∑ i, p i * QZ i j) * hh j
      = (18 : R) * z * ((n : R) * g - ∑ i, iota (p i) * hh i)
        + ∑ i, iota (p i) * ((18 : R) * (z * hh i) - ∑ j, iota (QZ i j) * hh j) := by
    push_cast
    simp only [Fin.sum_univ_eight, map_add, map_mul]
    ring
  rw [key]
  exact P.add_mem (Ideal.mul_mem_left _ _ hp)
    (Ideal.sum_mem _ (fun i _ => Ideal.mul_mem_left _ _ (key_z i)))
end MohP3
