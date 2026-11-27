-- Prove2me | solution 1 for MohP3.FormalLocal.iter_yOrd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:32:57.38212+00:00
-- url     : https://prove2.me/submissions/b443b6a2-6f10-422a-9d81-05517a80bcf5

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
public import Theorems.Thm_MohP3_Wt_wt_dd
public import Theorems.Thm_MohP3_Wt_yOrd_mono
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
theorem _root_.solution (F : Sk k) (s : ℕ) (i : Fin 8) :
    YOrd ((iter k F (s + 1)).2.1 i) (s - 30) :=
  yOrd_mono (by have : Gen.sig i ≤ 30 := by fin_cases i <;> simp [Gen.sig]
                omega)
    ((stepFun_spec k s _ (iter_wOrd k F s)).2.1 i)
end MohP3.FormalLocal
