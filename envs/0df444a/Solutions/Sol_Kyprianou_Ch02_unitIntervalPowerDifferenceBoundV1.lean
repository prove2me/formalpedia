-- Prove2me | solution 1 for Kyprianou.Ch02.unitIntervalPowerDifferenceBoundV1
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T00:31:49.535489+00:00
-- url     : https://prove2.me/submissions/13f18d04-54fa-4e2c-b062-5139bc2641f0

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false


theorem solution (x y : ℝ) (hx : x ∈ Set.Icc 0 1) (hy : y ∈ Set.Icc 0 1) (N : ℕ) :
    |x^N-y^N| ≤ |x-y| * (N : ℝ) := by
  induction N with
  | zero => simp
  | succ n ih =>
    have hx' := abs_of_nonneg hx.1
    have hy' := abs_of_nonneg (pow_nonneg hy.1 n)
    have hpow := pow_le_one₀ hy.1 hy.2 (n := n)
    have step : x^(n+1)-y^(n+1) = x*(x^n-y^n) + y^n*(x-y) := by ring
    rw [step]; calc
      _ ≤ |x*(x^n-y^n)| + |y^n*(x-y)| := abs_add_le _ _
      _ ≤ |x-y| * (n:ℝ) + |x-y| := by
        simp only [abs_mul,hx',hy']; apply add_le_add
        · exact (mul_le_of_le_one_left (abs_nonneg _) hx.2).trans ih
        · exact mul_le_of_le_one_left (abs_nonneg _) hpow
      _ = _ := by push_cast; ring
