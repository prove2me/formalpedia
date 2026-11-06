-- Prove2me | solution 1 for LostSalesExpGap.ConstOrder.lemma_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T08:11:56.76561+00:00
-- url     : https://prove2.me/submissions/653440e9-ce0a-4e7f-9572-500a238ab3bf
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LostSalesExpGap_ConstOrder_ConstantOrder
import Theorems.Thm_LostSalesExpGap_ConstOrder_opt_ge_CL
import Theorems.Thm_LostSalesExpGap_ConstOrder_eq_3
import Theorems.Thm_LostSalesExpGap_ConstOrder_best_constant_exists

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

open LostSalesExpGap.ConstOrder CappedBaseStock in
theorem solution (P : CappedBaseStock.DemandLaw) (c : CappedBaseStock.Parameters)
    (hP : LostSalesConstantOrder.LargeLeadTime.NonDeterministic P) :
    ENNReal.ofReal (CL P c (rL P c c.L) c.L) ≤ CappedBaseStock.OPT P c ∧
      constCost P c (rInf P c) ≠ ⊤ ∧ CappedBaseStock.OPT P c ≠ ⊤ ∧ EIinf P (rInf P c) ≠ ⊤ ∧
      (constCost P c (rInf P c)).toReal - (CappedBaseStock.OPT P c).toReal ≤
        c.h * ((EIinf P (rInf P c)).toReal - EIL P (rInf P c) c.L) +
          c.h * (EIL P (rInf P c) c.L - EIL P (rL P c c.L) c.L) -
          c.p * (rInf P c - rL P c c.L) := by
  have hlow := opt_ge_CL P c hP
  obtain ⟨_, _, hrmem, hrlt⟩ := best_constant_exists P c hP
  have hh := c.holding_pos
  have hp := c.penalty_pos
  set r := rInf P c
  set m := mean P
  have hm : 0 < m := P.positiveMean
  have hr0 : 0 ≤ r := hrmem.1.1
  -- `E[I^0_∞] = 0`
  have hE0 : EIinf P 0 = 0 := by
    unfold EIinf
    have : ∀ d : DemandPath, LostSalesConstantOrder.LargeLeadTime.supWalk (0 : ℝ).toNNReal d = 0 := by
      intro d
      unfold LostSalesConstantOrder.LargeLeadTime.supWalk
      apply ENNReal.iSup_eq_zero.mpr
      intro k
      apply ENNReal.ofReal_of_nonpos
      unfold LostSalesConstantOrder.LargeLeadTime.walk
      have : 0 ≤ ∑ i ∈ Finset.Icc 1 k, (d (i - 1) : ℝ) := by positivity
      simp only [Real.toNNReal_zero, NNReal.coe_zero, mul_zero, zero_sub, neg_nonpos]
      exact this
    have h0 : (0 : ℝ).toNNReal = 0 := Real.toNNReal_zero
    simp only [h0] at this
    simp only [Real.toNNReal_zero, this, lintegral_zero]
  have hC0 : constCost P c 0 = ENNReal.ofReal (c.p * m) := by
    rw [eq_3 P c 0 le_rfl hm, hE0, mul_zero, zero_add, sub_zero]
  have hCfin : constCost P c r ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (hrmem.2 0 ⟨le_rfl, hm.le⟩)
    rw [hC0]; exact ENNReal.ofReal_ne_top
  have hCeq := eq_3 P c r hr0 hrlt
  have hEfin : EIinf P r ≠ ⊤ := by
    intro htop
    rw [hCeq, htop, ENNReal.mul_top (by simp [hh]), top_add] at hCfin
    exact hCfin rfl
  have hOPTle : OPT P c ≤ constCost P c r :=
    iInf_le (fun π => policyCost P c π) (constOrderPolicy r.toNNReal)
  have hOfin : OPT P c ≠ ⊤ := ne_top_of_le_ne_top hCfin hOPTle
  refine ⟨hlow, hCfin, hOfin, hEfin, ?_⟩
  have hCL : CL P c (rL P c c.L) c.L ≤ (OPT P c).toReal :=
    (ENNReal.ofReal_le_iff_le_toReal hOfin).mp hlow
  have hCreal : (constCost P c r).toReal = c.h * (EIinf P r).toReal + c.p * (m - r) := by
    rw [hCeq, ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hEfin)
      ENNReal.ofReal_ne_top, ENNReal.toReal_mul, ENNReal.toReal_ofReal hh.le,
      ENNReal.toReal_ofReal (by nlinarith)]
  rw [hCreal]
  simp only [CL] at hCL
  linarith
