-- Prove2me | solution 1 for Kyprianou.Ch01.queueWorkload_initial_difference_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T19:33:04.723183+00:00
-- url     : https://prove2.me/submissions/f4b850f0-39d1-4d9e-90f9-515b8498ecc5

import Mathlib
import Definitions.Def_Kyprianou_Ch01_RiskQueueCore
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (arrival claims : ℕ → Ω → ℝ) (t : ℝ≥0) (ω : Ω)
    (w1 w2 : ℝ) (h : w1 ≤ w2) :
    queueWorkload arrival claims w2 t ω -
      queueWorkload arrival claims w1 t ω ≤ w2 - w1 := by
  unfold queueWorkload
  let S : ℝ := sSup {z : ℝ | ∃ s : ℝ≥0,
    s ≤ t ∧ z = riskSurplus arrival claims 1 0 s ω}
  have h1 : w1 ≤ max w1 S := le_max_left _ _
  have h2 : S ≤ max w1 S := le_max_right _ _
  have hmax : max w2 S ≤ max w1 S + (w2 - w1) := by
    apply max_le
    · linarith
    · linarith
  dsimp [S] at hmax
  linarith
