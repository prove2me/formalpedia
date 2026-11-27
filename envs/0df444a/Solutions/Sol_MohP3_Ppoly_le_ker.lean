-- Prove2me | solution 1 for MohP3.Ppoly_le_ker
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:32:14.415113+00:00
-- url     : https://prove2.me/submissions/f6a4c34e-2e28-4815-bf44-4ae5f00a78de

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
public import Theorems.Thm_MohP3_rho_k_ffK
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
omit [CharZero k]
namespace MohP3
theorem _root_.solution : Ppoly k ≤ RingHom.ker (rho_k k) := by
  rw [Ppoly, Gen.P, Ideal.span_le]
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact RingHom.mem_ker.mpr (rho_k_ffK k 0)
  · exact RingHom.mem_ker.mpr (rho_k_ffK k 1)
  · exact RingHom.mem_ker.mpr (rho_k_ffK k 2)
  · exact RingHom.mem_ker.mpr (rho_k_ffK k 3)
end MohP3
