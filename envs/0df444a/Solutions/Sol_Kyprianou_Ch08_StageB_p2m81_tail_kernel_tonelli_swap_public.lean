-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m81_tail_kernel_tonelli_swap_public
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T07:30:06.812348+00:00
-- url     : https://prove2.me/submissions/483c4996-f41a-4fd2-864a-3162bdc88628

import Mathlib
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m81_tail_kernel_tonelli_lhs_public
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m81_tail_kernel_tonelli_rhs_ptwise_public
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (s : ℝ) (ρ : Measure ℝ) (hprob : IsProbabilityMeasure ρ) :
    (∫⁻ y in Ici (0 : ℝ), (∫⁻ z in Ioi y, ENNReal.ofReal (Real.exp (-s * y)) ∂ρ) ∂volume) =
      ∫⁻ z, (∫⁻ y in Ico (0 : ℝ) z, ENNReal.ofReal (Real.exp (-s * y)) ∂volume) ∂ρ := by
  haveI := hprob
  have hSet : MeasurableSet {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 < p.2} := by
    simpa only [Set.setOf_and] using
      (measurableSet_le measurable_const measurable_fst).inter
        (measurableSet_lt measurable_fst measurable_snd)
  have hFun : Measurable
      (fun p : ℝ × ℝ => ENNReal.ofReal (Real.exp (-s * p.1))) :=
    ENNReal.continuous_ofReal.measurable.comp
      (Real.continuous_exp.measurable.comp
        (measurable_fst.const_mul (-s)))
  have hUncMeas : Measurable (Function.uncurry (fun y z : ℝ =>
      if 0 ≤ y ∧ y < z then
        ENNReal.ofReal (Real.exp (-s * y)) else 0)) :=
    Measurable.ite hSet hFun measurable_const
  have hAEMeas : AEMeasurable (Function.uncurry (fun y z : ℝ =>
      if 0 ≤ y ∧ y < z then
        ENNReal.ofReal (Real.exp (-s * y)) else 0)) (volume.prod ρ) :=
    hUncMeas.aemeasurable
  have hSwap := lintegral_lintegral_swap hAEMeas
  have hLHS_swap := Kyprianou.Ch08.StageB.p2m81_tail_kernel_tonelli_lhs_public s ρ hprob
  have hRHS_pt := fun z =>
    Kyprianou.Ch08.StageB.p2m81_tail_kernel_tonelli_rhs_ptwise_public s z
  have hRHS_swap := lintegral_congr (μ := ρ) hRHS_pt
  exact hLHS_swap.symm.trans (hSwap.trans hRHS_swap)
