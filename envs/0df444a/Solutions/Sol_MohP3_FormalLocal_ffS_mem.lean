-- Prove2me | solution 1 for MohP3.FormalLocal.ffS_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:31:52.613233+00:00
-- url     : https://prove2.me/submissions/f363a043-6d94-4a0d-ba02-420023af553b

module
public import Definitions.Def_MohP3_FormalLocal
public import Definitions.Def_MohP3_GenClosure
public import Definitions.Def_MohP3_Order
public import Definitions.Def_MohP3_Generation
public import Theorems.Thm_MohP3_Gen_f1_mem
public import Theorems.Thm_MohP3_Gen_f2_mem
public import Theorems.Thm_MohP3_Gen_f3_mem
public import Theorems.Thm_MohP3_Gen_f4_mem


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPowerSeries MohP3.Wt
open MohP3 MohP3.FormalLocal
variable (k : Type*) [Field k] [CharZero k]
omit [CharZero k]
namespace MohP3.FormalLocal
theorem _root_.solution (j : Fin 4) : ffS k j ∈ Pk k := by
  fin_cases j
  exacts [Gen.f1_mem _ _ _, Gen.f2_mem _ _ _, Gen.f3_mem _ _ _, Gen.f4_mem _ _ _]
end MohP3.FormalLocal
