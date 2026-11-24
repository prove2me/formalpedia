-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m810_sampled_drawdown_clock_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T08:05:35.421696+00:00
-- url     : https://prove2.me/submissions/cd8892bc-abde-4756-b5e5-e12f79ea7404


import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Source record regeneration. -/
theorem solution :
    ∀ (s : ℕ → ℝ≥0) (a : ℝ),
      Measurable (fun f : ℝ≥0 → ℝ => ⨅ i : ℕ,
        if f (s i) - (⨆ j : ℕ, if s j ≤ s i
          then ENNReal.ofReal (f (s j)) else 0).toReal < -a
        then (s i : ℝ≥0∞) else ⊤) := by
  intro s a
  have hM (i : ℕ) : Measurable (fun f : ℝ≥0 → ℝ =>
      (⨆ j : ℕ, if s j ≤ s i then ENNReal.ofReal (f (s j)) else 0).toReal) := by
    apply ENNReal.measurable_toReal.comp
    apply Measurable.iSup
    intro j
    by_cases h : s j ≤ s i
    · simpa [h, Function.comp_def] using ENNReal.measurable_ofReal.comp (measurable_pi_apply (s j))
    · simpa [h] using (measurable_const : Measurable (fun _ : ℝ≥0 → ℝ => (0:ℝ≥0∞)))
  apply Measurable.iInf
  intro i
  exact Measurable.ite (measurableSet_lt ((measurable_pi_apply (s i)).sub (hM i))
    measurable_const) measurable_const measurable_const
