-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m810_shifted_killed_discount
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T08:20:46.629664+00:00
-- url     : https://prove2.me/submissions/2413fc25-8aef-4792-a1fe-8a93bd4cdd99


import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Exact first-record clock reduction. -/
theorem solution :
    ∀ (q : ℝ) (u : ℝ≥0) (U R : ℝ≥0∞),
      (if (u : ℝ≥0∞)+U < (u : ℝ≥0∞)+R
        then discountedAt q ((u : ℝ≥0∞)+U) else 0) =
      Real.exp (-q*(u:ℝ)) * (if U < R then discountedAt q U else 0) := by
  intro q u U R
  by_cases h : U < R
  · have hh := (ENNReal.add_lt_add_iff_left (a := (u:ℝ≥0∞)) ENNReal.coe_ne_top).2 h
    rw [if_pos hh,if_pos h]
    cases U with
    | top => exact (not_top_lt h).elim
    | coe v =>
      rw [← ENNReal.coe_add]
      simp only [discountedAt,NNReal.coe_add,← Real.exp_add]
      congr 1
      ring
  · have hh : ¬ (u:ℝ≥0∞)+U < (u:ℝ≥0∞)+R :=
      fun he => h ((ENNReal.add_lt_add_iff_left (a := (u:ℝ≥0∞)) ENNReal.coe_ne_top).1 he)
    rw [if_neg hh,if_neg h,mul_zero]
