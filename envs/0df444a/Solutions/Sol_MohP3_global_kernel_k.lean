-- Prove2me | solution 1 for MohP3.global_kernel_k
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:35:05.686104+00:00
-- url     : https://prove2.me/submissions/3920f0b0-cd0d-4f9f-955f-265eb5f4a4f2

module
public import Definitions.Def_MohP3_GenClosure
public import Definitions.Def_MohP3_IndependenceK
public import Definitions.Def_MohP3_GlobalK
public import Theorems.Thm_MohP3_rho_k_C
public import Theorems.Thm_MohP3_rho_k_xk
public import Theorems.Thm_MohP3_rho_k_yk
public import Theorems.Thm_MohP3_rho_k_zk
public import Theorems.Thm_MohP3_iotaK_X
public import Theorems.Thm_MohP3_iotaK_C
public import Theorems.Thm_MohP3_ffK_mem
public import Theorems.Thm_MohP3_rho_k_ffK
public import Theorems.Thm_MohP3_rho_k_hhK
public import Theorems.Thm_MohP3_rho_k_iotaK
public import Theorems.Thm_MohP3_RepP_all
public import Theorems.Thm_MohP3_Ppoly_le_ker
public import Theorems.Thm_MohP3_K_indepK

attribute [local simp] MohP3.rho_k_C
attribute [local simp] MohP3.rho_k_xk
attribute [local simp] MohP3.rho_k_yk
attribute [local simp] MohP3.rho_k_zk
attribute [local simp] MohP3.iotaK_X
attribute [local simp] MohP3.iotaK_C

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3
variable (k : Type*) [Field k] [CharZero k]
namespace MohP3
theorem _root_.solution : RingHom.ker (rho_k k) = Ppoly k := by
  refine le_antisymm ?_ (Ppoly_le_ker k)
  intro g hg
  obtain ⟨p, c, hp⟩ := RepP_all k g
  have hsum : ∑ i, (p i).comp (Polynomial.X ^ 8) * K.vvK k i = 0 := by
    have h0 : rho_k k g = 0 := RingHom.mem_ker.mp hg
    rw [hp, map_add, map_sum, map_sum] at h0
    have hz : ∑ j, rho_k k (c j * ffK k j) = 0 := by
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [map_mul, rho_k_ffK, mul_zero]
    rw [hz, add_zero] at h0
    rw [← h0]
    exact Finset.sum_congr rfl fun i _ => by rw [map_mul, rho_k_iotaK, rho_k_hhK]
  have hp0 := K.indepK k p hsum
  have hzero : (∑ i, iotaK k (p i) * hhK k i) = 0 :=
    Finset.sum_eq_zero fun i _ => by simp [hp0 i]
  rw [hp, hzero, zero_add]
  exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (ffK_mem k j)
end MohP3
