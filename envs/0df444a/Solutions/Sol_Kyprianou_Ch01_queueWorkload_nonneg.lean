-- Prove2me | solution 1 for Kyprianou.Ch01.queueWorkload_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T19:37:04.409717+00:00
-- url     : https://prove2.me/submissions/71bdde77-71b9-4827-8391-bee9a65e207c

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
    (arrival claims : ℕ → Ω → ℝ)
    (w : ℝ) (t : ℝ≥0) (ω : Ω)
    (hbounded : BddAbove {z : ℝ | ∃ s : ℝ≥0,
      s ≤ t ∧ z = riskSurplus arrival claims 1 0 s ω}) :
    0 ≤ queueWorkload arrival claims w t ω := by
  let S : Set ℝ := {z : ℝ | ∃ s : ℝ≥0,
    s ≤ t ∧ z = riskSurplus arrival claims 1 0 s ω}
  have hmem : riskSurplus arrival claims 1 0 t ω ∈ S :=
    ⟨t, le_rfl, rfl⟩
  have hsup : riskSurplus arrival claims 1 0 t ω ≤ sSup S :=
    le_csSup hbounded hmem
  have hmax : sSup S ≤ max w (sSup S) := le_max_right w (sSup S)
  change 0 ≤ max w (sSup S) -
    riskSurplus arrival claims 1 0 t ω
  linarith
