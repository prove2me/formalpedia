-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.actualRowCount_eventually_polynomial_upper
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T23:27:52.513001+00:00
-- url     : https://prove2.me/submissions/5abd149b-f55d-447b-9d89-8770dd517f2e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_actualRowCount_eventually_polynomial_upper_core

open Filter
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open scoped Topology

theorem solution
    {nu : ℝ} (d : FixedData nu) :
    ∃ C : ℝ, 0 < C ∧
      (∀ᶠ H : ℝ in atTop,
        (actualRowCount d H : ℝ) ≤ C * (H + 1) ^ (d.m + 1)) := by
  obtain ⟨C, hC⟩ :=
    OAI.PiExponent.DeterminantContradiction.actualRowCount_eventually_polynomial_upper_core d
  refine ⟨max C 1, by positivity, ?_⟩
  filter_upwards [hC, eventually_ge_atTop (0 : ℝ)] with H hH hHnonneg
  have hpow : 0 ≤ (H + 1) ^ (d.m + 1) := by
    positivity
  exact le_trans hH (mul_le_mul_of_nonneg_right (le_max_left C 1) hpow)