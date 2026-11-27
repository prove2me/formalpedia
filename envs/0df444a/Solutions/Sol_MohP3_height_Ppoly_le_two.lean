-- Prove2me | solution 1 for MohP3.height_Ppoly_le_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:40:19.653777+00:00
-- url     : https://prove2.me/submissions/a46c9480-c598-43ac-a822-e623ea9b430a

module
public import Definitions.Def_MohP3_GlobalK
public import Definitions.Def_MohP3_Ara
public import Definitions.Def_MohP3_HeightK
public import Theorems.Thm_MohP3_Ppoly_mem_minimalPrimes_Qpoly
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
open scoped Classical
namespace MohP3
theorem _root_.solution : (Ppoly k).height ≤ 2 := by
  have hQ : Qpoly k = Ideal.span
      ((({Gen.H1 (xk k) (yk k) (zk k), Gen.H2 (xk k) (yk k) (zk k)} : Finset (Rk k)) :
        Set (Rk k))) := by
    simp [Qpoly, Gen.Q]
  have h := Ideal.height_le_card_of_mem_minimalPrimes_span_finset
    (p := Ppoly k)
    (s := ({Gen.H1 (xk k) (yk k) (zk k), Gen.H2 (xk k) (yk k) (zk k)} : Finset (Rk k)))
    (by rw [← hQ]; exact Ppoly_mem_minimalPrimes_Qpoly k)
  refine h.trans ?_
  have : ({Gen.H1 (xk k) (yk k) (zk k), Gen.H2 (xk k) (yk k) (zk k)} :
      Finset (Rk k)).card ≤ 2 := Finset.card_insert_le _ _ |>.trans (by simp)
  exact_mod_cast this
end MohP3
