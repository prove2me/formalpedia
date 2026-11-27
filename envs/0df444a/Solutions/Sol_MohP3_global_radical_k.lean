-- Prove2me | solution 1 for MohP3.global_radical_k
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:37:11.308883+00:00
-- url     : https://prove2.me/submissions/85001ed0-20ec-4c89-a802-901380f39c14

module
public import Definitions.Def_MohP3_GenClosure
public import Definitions.Def_MohP3_IndependenceK
public import Definitions.Def_MohP3_GlobalK
public import Theorems.Thm_MohP3_Ppoly_isPrime
public import Theorems.Thm_MohP3_Gen_P_sq_le_Q
public import Theorems.Thm_MohP3_Gen_Q_le_P


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3
variable (k : Type*) [Field k] [CharZero k]
namespace MohP3
theorem _root_.solution : Ideal.radical (Qpoly k) = Ppoly k := by
  refine le_antisymm ?_ ?_
  · calc (Qpoly k).radical ≤ (Ppoly k).radical :=
          Ideal.radical_mono (Gen.Q_le_P (xk k) (yk k) (zk k))
      _ = Ppoly k := (Ppoly_isPrime k).radical
  · intro a ha
    exact ⟨2, Gen.P_sq_le_Q (xk k) (yk k) (zk k) (Ideal.pow_mem_pow ha 2)⟩
end MohP3
