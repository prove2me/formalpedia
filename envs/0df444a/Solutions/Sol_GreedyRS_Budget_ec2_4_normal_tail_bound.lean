-- Prove2me | solution 1 for GreedyRS.Budget.ec2_4_normal_tail_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T11:39:17.489412+00:00
-- url     : https://prove2.me/submissions/46de9e18-f925-4650-a262-6be2f75eba1f

import Mathlib
import Definitions.Def_GreedyRS_Greedy_Setting

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

theorem solution (t : ℝ) (ht : 0 < t) :
    1 - GreedyRS.Greedy.Phi t ≤ Real.exp (-t ^ 2 / 2) := by
  have h1 : 1 - GreedyRS.Greedy.Phi t = (gaussianReal 0 1).real (Set.Ioi t) := by
    rw [GreedyRS.Greedy.Phi, cdf_eq_real, ← Set.compl_Iic,
      probReal_compl_eq_one_sub measurableSet_Iic]
  rw [h1]
  calc (gaussianReal 0 1).real (Set.Ioi t)
      ≤ (gaussianReal 0 1).real {x | t ≤ id x} := by
        apply measureReal_mono
        · intro x (hx : t < x); exact le_of_lt hx
        · exact measure_ne_top _ _
    _ ≤ Real.exp (-t * t) * mgf id (gaussianReal 0 1) t :=
        measure_ge_le_exp_mul_mgf t ht.le (integrable_exp_mul_gaussianReal t)
    _ = Real.exp (-t ^ 2 / 2) := by
        rw [mgf_gaussianReal (μ := 0) (v := 1) (by simp), ← Real.exp_add]
        congr 1; push_cast; ring
