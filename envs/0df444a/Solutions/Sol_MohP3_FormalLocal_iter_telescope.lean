-- Prove2me | solution 1 for MohP3.FormalLocal.iter_telescope
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:33:13.844506+00:00
-- url     : https://prove2.me/submissions/c7feecca-317a-4973-a5a9-eeb935a84ccf

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
theorem _root_.solution (F : Sk k) (M : ℕ) :
    F - (iter k F M).1 =
      (∑ i, iotaS k (∑ s ∈ Finset.range M, (iter k F (s + 1)).2.1 i) * hhS k i) +
        ∑ j, (∑ s ∈ Finset.range M, (iter k F (s + 1)).2.2 j) * ffS k j := by
  induction M with
  | zero => simp [iter]
  | succ M ih =>
      have hstep := (stepFun_spec k M (iter k F M).1 (iter_wOrd k F M)).2.2.2
      have hnext : iter k F (M + 1) = stepFun k M (iter k F M).1 := rfl
      rw [← hnext] at hstep
      simp only [Finset.sum_range_succ, map_add, Fin.sum_univ_eight, Fin.sum_univ_four,
        add_mul] at ih hstep ⊢
      linear_combination ih + hstep
end MohP3.FormalLocal
