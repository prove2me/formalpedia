-- Prove2me | solution 1 for Kyprianou.Ch02.laplacePowerDefectBoundV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T00:03:44.935943+00:00
-- url     : https://prove2.me/submissions/4c8cb4bf-2f66-4027-bae5-5fae10e01d90

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Probability.ConditionalProbability
import Mathlib.Tactic.Positivity
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    (a : ℕ → ℝ) (α : ℝ) (ha : ∀ n, 0 ≤ a n)
    (hα : 0 < α) (ht : Tendsto (fun n => a n ^ (n+1)) atTop (nhds α)) :
    ∀ᶠ n in atTop, ((n+1 : ℕ) : ℝ)*(1-a n) ≤ -Real.log (α/2) := by
  filter_upwards [(tendsto_order.mp ht).1 (α/2) (by linarith)] with n hn
  have hle : a n ≤ Real.exp (a n-1) := by
    linarith [Real.add_one_le_exp (a n-1)]
  have hp := pow_le_pow_left₀ (ha n) hle (n+1)
  rw [← Real.exp_nat_mul] at hp
  have hh := (Real.log_le_iff_le_exp (show 0 < α/2 by positivity)).2 (hn.le.trans hp)
  push_cast at hh ⊢
  linarith
