-- Prove2me | solution 1 for MohP3.FormalLocal.iter_wOrd_c
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:33:13.228538+00:00
-- url     : https://prove2.me/submissions/b0f21e2f-42ae-4ea9-a44e-64430cd13107

module
public import Definitions.Def_MohP3_FormalLocal
public import Definitions.Def_MohP3_GenClosure
public import Definitions.Def_MohP3_Order
public import Definitions.Def_MohP3_Generation
public import Theorems.Thm_MohP3_FormalLocal_stepFun_spec
public import Theorems.Thm_MohP3_FormalLocal_iter_wOrd
public import Theorems.Thm_MohP3_Wt_dd_apply_one
public import Theorems.Thm_MohP3_Wt_dd_apply_two
public import Theorems.Thm_MohP3_Wt_dd_apply_zero
public import Theorems.Thm_MohP3_Wt_wOrd_mono
public import Theorems.Thm_MohP3_Wt_wt_dd
attribute [local simp] MohP3.Wt.dd_apply_one
attribute [local simp] MohP3.Wt.dd_apply_two
attribute [local simp] MohP3.Wt.dd_apply_zero
attribute [local simp] MohP3.Wt.wt_dd



set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPowerSeries MohP3.Wt
open MohP3 MohP3.FormalLocal
variable (k : Type*) [Field k] [CharZero k]
namespace MohP3.FormalLocal
theorem _root_.solution (F : Sk k) (s : ℕ) (j : Fin 4) :
    WOrd ((iter k F (s + 1)).2.2 j) (s - 30) :=
  wOrd_mono (by have : Gen.tau j ≤ 30 := by fin_cases j <;> simp [Gen.tau]
                omega)
    ((stepFun_spec k s _ (iter_wOrd k F s)).2.2.1 j)
end MohP3.FormalLocal
