-- Prove2me | solution 1 for MohP3.ffK_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:26:30.374889+00:00
-- url     : https://prove2.me/submissions/3d4b80f7-19ce-4091-a8ee-b0040f02b7e5

module
public import Definitions.Def_MohP3_GenClosure
public import Definitions.Def_MohP3_IndependenceK
public import Definitions.Def_MohP3_GlobalK
public import Theorems.Thm_MohP3_Gen_f1_mem
public import Theorems.Thm_MohP3_Gen_f2_mem
public import Theorems.Thm_MohP3_Gen_f3_mem
public import Theorems.Thm_MohP3_Gen_f4_mem


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3
variable (k : Type*) [Field k] [CharZero k]
omit [CharZero k]
namespace MohP3
theorem _root_.solution (j : Fin 4) : ffK k j ∈ Ppoly k := by
  fin_cases j
  exacts [Gen.f1_mem _ _ _, Gen.f2_mem _ _ _, Gen.f3_mem _ _ _, Gen.f4_mem _ _ _]
end MohP3
