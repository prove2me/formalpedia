-- Prove2me | solution 1 for MohP3.arithRank_Ppoly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:42:55.851382+00:00
-- url     : https://prove2.me/submissions/1237dad7-7105-4572-bd68-afa1d65635ca

module
public import Definitions.Def_MohP3_GlobalK
public import Definitions.Def_MohP3_Ara
public import Definitions.Def_MohP3_HeightK
public import Theorems.Thm_MohP3_sigmaK_xk
public import Theorems.Thm_MohP3_sigmaK_yk
public import Theorems.Thm_MohP3_sigmaK_zk
public import Theorems.Thm_MohP3_height_Ppoly
public import Theorems.Thm_MohP3_Ppoly_isPrime
public import Theorems.Thm_MohP3_arithRank_le
public import Theorems.Thm_MohP3_global_radical_k
public import Theorems.Thm_MohP3_height_le_arithRank
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


attribute [local simp] MohP3.sigmaK_xk
attribute [local simp] MohP3.sigmaK_yk
attribute [local simp] MohP3.sigmaK_zk

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3
variable (k : Type*) [Field k] [CharZero k]
open scoped Classical
namespace MohP3
theorem _root_.solution : arithRank (Ppoly k) = 2 := by
  refine le_antisymm ?_ ?_
  · refine le_trans (arithRank_le
      ({Gen.H1 (xk k) (yk k) (zk k), Gen.H2 (xk k) (yk k) (zk k)} : Finset (Rk k)) ?_) ?_
    · have hQ : Ideal.span
          ((({Gen.H1 (xk k) (yk k) (zk k), Gen.H2 (xk k) (yk k) (zk k)} : Finset (Rk k)) :
            Set (Rk k))) = Qpoly k := by
        simp [Qpoly, Gen.Q]
      rw [hQ, global_radical_k, (Ppoly_isPrime k).radical]
    · have : ({Gen.H1 (xk k) (yk k) (zk k), Gen.H2 (xk k) (yk k) (zk k)} :
          Finset (Rk k)).card ≤ 2 := Finset.card_insert_le _ _ |>.trans (by simp)
      exact_mod_cast this
  · calc (2 : ℕ∞) = (Ppoly k).height := (height_Ppoly k).symm
      _ ≤ arithRank (Ppoly k) := height_le_arithRank (Ppoly k) (Ppoly_isPrime k)
end MohP3
