-- Prove2me | solution 1 for MohP3.radical_Q
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:24:58.304571+00:00
-- url     : https://prove2.me/submissions/4371330c-ca02-436f-9cab-79eba14014a3

module
public import Definitions.Def_MohP3_Kernel
public import Definitions.Def_MohP3_Global
public import Theorems.Thm_MohP3_P_radical
public import Theorems.Thm_MohP3_Gen_P_sq_le_Q
public import Theorems.Thm_MohP3_Gen_Q_le_P
public import Theorems.Thm_MohP3_P_sq_le_Q
public import Theorems.Thm_MohP3_Q_le_P


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3
namespace MohP3
theorem _root_.solution : Ideal.radical Q = P := by
  refine le_antisymm ?_ ?_
  · calc Q.radical ≤ P.radical := Ideal.radical_mono Q_le_P
      _ = P := P_radical
  · intro a ha
    exact ⟨2, P_sq_le_Q (Ideal.pow_mem_pow ha 2)⟩
end MohP3
