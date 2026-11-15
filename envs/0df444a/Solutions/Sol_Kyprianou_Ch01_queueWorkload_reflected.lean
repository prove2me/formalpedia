-- Prove2me | solution 1 for Kyprianou.Ch01.queueWorkload_reflected
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T21:11:34.147329+00:00
-- url     : https://prove2.me/submissions/44222402-de9a-4e32-bdf7-d5e1fdeade16

import Mathlib
import Definitions.Def_Kyprianou_Ch01_RiskQueueCore

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal Pointwise
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (arrival claims : ℕ → Ω → ℝ)
    (w : ℝ) (t : ℝ≥0) (ω : Ω)
    (hbounded : BddAbove {z : ℝ | ∃ s : ℝ≥0,
      s ≤ t ∧ z = riskSurplus arrival claims 1 0 s ω}) :
    let a := riskSurplus arrival claims 1 0 t ω
    let S : Set ℝ := {z | ∃ s : ℝ≥0,
      s ≤ t ∧ z = riskSurplus arrival claims 1 0 s ω}
    queueWorkload arrival claims w t ω =
      max (w - a) (sSup (S - {a})) := by
  dsimp
  let a := riskSurplus arrival claims 1 0 t ω
  let S : Set ℝ := {z | ∃ s : ℝ≥0,
    s ≤ t ∧ z = riskSurplus arrival claims 1 0 s ω}
  have hmem : a ∈ S := ⟨t, le_rfl, rfl⟩
  have hnonempty : S.Nonempty := ⟨a, hmem⟩
  have hshift : sSup (S - {a}) = sSup S - a := by
    simpa using (csSup_sub hnonempty hbounded
      (Set.singleton_nonempty a) (bddBelow_singleton : BddBelow ({a} : Set ℝ)))
  change max w (sSup S) - a = max (w - a) (sSup (S - {a}))
  rw [hshift]
  rcases le_total w (sSup S) with hw | hw
  · rw [max_eq_right hw, max_eq_right (sub_le_sub_right hw a)]
  · rw [max_eq_left hw, max_eq_left (sub_le_sub_right hw a)]
