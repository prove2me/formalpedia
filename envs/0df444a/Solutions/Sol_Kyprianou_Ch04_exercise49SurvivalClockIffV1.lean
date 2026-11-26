-- Prove2me | solution 1 for Kyprianou.Ch04.exercise49SurvivalClockIffV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T16:05:25.103903+00:00
-- url     : https://prove2.me/submissions/55fa9524-c0c4-4d49-84d9-6daaa619200e

import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Probability.ConditionalProbability
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false
/-- For a zero-start path, infinite strict downcrossing at nonnegative reserve is equivalent to a global lower bound. -/
theorem solution
    (Y : NNReal → ℝ) (h0 : Y 0 = 0) (x : ℝ) (hx : 0 ≤ x) :
    (sInf {v : WithTop NNReal | ∃ t : NNReal,
      v = ↑t ∧ 0 < t ∧ x + Y t < 0}) = ⊤ ↔
      ∀ t : NNReal, -x ≤ Y t := by
  constructor
  · intro h t
    by_contra! hn
    have ht : 0 < t := by
      by_contra! h
      have he : t = 0 := le_antisymm h bot_le
      rw [he, h0] at hn
      linarith
    have hle : (sInf {v : WithTop NNReal | ∃ u : NNReal,
        v = ↑u ∧ 0 < u ∧ x + Y u < 0}) ≤ ↑t :=
      sInf_le ⟨t, rfl, ht, by linarith⟩
    rw [h] at hle
    exact WithTop.coe_ne_top (top_le_iff.mp hle)
  · intro h
    by_contra hn
    obtain ⟨_, ⟨t, rfl, _, ht⟩, _⟩ := sInf_lt_iff.mp (lt_top_iff_ne_top.mpr hn)
    linarith [h t]
