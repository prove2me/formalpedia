-- Prove2me | solution 1 for Kyprianou.Ch01.expSourceEqualsArrivalDensity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T07:31:22.383388+00:00
-- url     : https://prove2.me/submissions/70e960fb-2727-48a0-b433-900abec13eb4

import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Definitions.Def_levy_foundations_arrivalGammaDensity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution (beta : ℝ) (hbeta : 0 < beta) :
    (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
      (fun x : ℝ => ENNReal.ofReal (beta * Real.exp (-beta * x))) =
      volume.withDensity (LevyFoundations.arrivalGammaDensity beta 0) := by
  rw [← withDensity_indicator measurableSet_Ioi]
  apply withDensity_congr_ae
  have h0 : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by
    rw [ae_iff]
    simpa using (volume_singleton (a := (0 : ℝ)))
  filter_upwards [h0] with x hx
  unfold LevyFoundations.arrivalGammaDensity
  unfold LevyFoundations.arrivalGammaDensityReal
  by_cases hp : 0 < x
  · have hn : x ∈ Set.Ici (0 : ℝ) := hp.le
    simp only [Set.indicator_of_mem (show x ∈ Set.Ioi (0 : ℝ) from hp),
      Set.indicator_of_mem hn]
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one,
      pow_one, mul_one]
    ring
  · have hn : x < 0 := by
      rcases lt_trichotomy x 0 with h | h | h
      · exact h
      · exact False.elim (hx h)
      · exact False.elim (hp h)
    have hnot : x ∉ Set.Ici (0 : ℝ) := not_le.mpr hn
    simp only [Set.indicator_of_notMem (show x ∉ Set.Ioi (0 : ℝ) from hp),
      Set.indicator_of_notMem hnot]
