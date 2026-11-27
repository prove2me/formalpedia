-- Prove2me | solution 1 for MohP3.FormalLocal.generation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:35:26.923584+00:00
-- url     : https://prove2.me/submissions/de232039-9e4f-413a-8eec-ce426a3f0cba

module
public import Definitions.Def_MohP3_FormalLocal
public import Definitions.Def_MohP3_GenClosure
public import Definitions.Def_MohP3_Order
public import Definitions.Def_MohP3_Generation
public import Theorems.Thm_MohP3_FormalLocal_ffS_mem
public import Theorems.Thm_MohP3_FormalLocal_iter_wOrd
public import Theorems.Thm_MohP3_FormalLocal_iter_yOrd
public import Theorems.Thm_MohP3_FormalLocal_iter_wOrd_c
public import Theorems.Thm_MohP3_FormalLocal_iter_telescope
public import Theorems.Thm_MohP3_Wt_dd_apply_one
public import Theorems.Thm_MohP3_Wt_dd_apply_two
public import Theorems.Thm_MohP3_Wt_dd_apply_zero
public import Theorems.Thm_MohP3_Wt_exists_wOrd_limit
public import Theorems.Thm_MohP3_Wt_exists_yOrd_limit
public import Theorems.Thm_MohP3_Wt_wOrd_eq_zero
public import Theorems.Thm_MohP3_Wt_wOrd_mono
public import Theorems.Thm_MohP3_Wt_wOrd_sub
public import Theorems.Thm_MohP3_Wt_wOrd_sum
public import Theorems.Thm_MohP3_Wt_wOrd_zero
public import Theorems.Thm_MohP3_Wt_wt_dd
public import Theorems.Thm_MohP3_Wt_yOrd_mono
public import Theorems.Thm_P2M_MohP3_Wt_wOrd_mul__c4d0f86c750f
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
theorem _root_.solution (k : Type*) [Field k] [CharZero k] : Generation k := by
  intro F
  choose Q hQ using fun i : Fin 8 =>
    exists_yOrd_limit (fun s => (iter k F (s + 1)).2.1 i) 30 (fun s => iter_yOrd k F s i)
  choose Cc hCc using fun j : Fin 4 =>
    exists_wOrd_limit (fun s => (iter k F (s + 1)).2.2 j) 30 (fun s => iter_wOrd_c k F s j)
  refine ⟨Q, ?_⟩
  have hzero : (F - ∑ i, iotaS k (Q i) * hhS k i) - ∑ j, Cc j * ffS k j = 0 := by
    refine wOrd_eq_zero ?_
    intro n
    set M := n + 30 with hM
    have htel := iter_telescope k F M
    have hD : (F - ∑ i, iotaS k (Q i) * hhS k i) - ∑ j, Cc j * ffS k j =
        ((iter k F M).1 -
          ∑ i, iotaS k (Q i - ∑ s ∈ Finset.range M, (iter k F (s + 1)).2.1 i) * hhS k i) -
          ∑ j, (Cc j - ∑ s ∈ Finset.range M, (iter k F (s + 1)).2.2 j) * ffS k j := by
      simp only [map_sub, sub_mul, Fin.sum_univ_eight, Fin.sum_univ_four] at htel ⊢
      linear_combination htel
    rw [hD]
    refine wOrd_sub (wOrd_sub (wOrd_mono (by omega) (iter_wOrd k F M)) ?_) ?_
    · refine wOrd_sum ?_
      intro i _
      exact wOrd_mul' (m := n) (n := 0) (by omega)
        (wOrd_iotaS k (yOrd_mono (by omega) (hQ i M))) (wOrd_zero _)
    · refine wOrd_sum ?_
      intro j _
      exact wOrd_mul' (m := n) (n := 0) (by omega)
        (wOrd_mono (by omega) (hCc j M)) (wOrd_zero _)
  have hEq : F - ∑ i, iotaS k (Q i) * hhS k i = ∑ j, Cc j * ffS k j := by
    have := sub_eq_zero.mp hzero
    exact this
  rw [hEq]
  exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (ffS_mem k j)
end MohP3.FormalLocal
