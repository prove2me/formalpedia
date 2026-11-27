-- Prove2me | solution 1 for MohP3.rho_k_eq_tauK_comp_sigmaK
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:34:39.150176+00:00
-- url     : https://prove2.me/submissions/35e1fa68-1b07-4852-a381-663c78146e11

module
public import Definitions.Def_MohP3_GlobalK
public import Definitions.Def_MohP3_Ara
public import Definitions.Def_MohP3_HeightK
public import Theorems.Thm_MohP3_iotaK_C
public import Theorems.Thm_MohP3_iotaK_X
public import Theorems.Thm_MohP3_rho_k_C
public import Theorems.Thm_MohP3_rho_k_xk
public import Theorems.Thm_MohP3_rho_k_yk
public import Theorems.Thm_MohP3_rho_k_zk
attribute [local simp] MohP3.iotaK_C
attribute [local simp] MohP3.iotaK_X
attribute [local simp] MohP3.rho_k_C
attribute [local simp] MohP3.rho_k_xk
attribute [local simp] MohP3.rho_k_yk
attribute [local simp] MohP3.rho_k_zk



set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3
variable (k : Type*) [Field k] [CharZero k]
omit [CharZero k]
namespace MohP3
theorem _root_.solution : rho_k k = (tauK k).comp (sigmaK k) := by
  refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
  · simp [sigmaK, tauK]
  · fin_cases i <;> simp [sigmaK, tauK, rho_k] <;> ring
end MohP3
