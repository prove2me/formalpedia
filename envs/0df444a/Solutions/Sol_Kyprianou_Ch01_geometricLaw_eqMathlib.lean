-- Prove2me | solution 1 for Kyprianou.Ch01.geometricLaw_eqMathlib
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:30:29.67743+00:00
-- url     : https://prove2.me/submissions/068e2964-0b5c-4144-91a5-95d3f753ebc4

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped ENNReal
set_option autoImplicit false

theorem solution
    (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (G : Measure ℕ)
    (hGeom : ∀ k : ℕ,
      G {k} = ENNReal.ofReal (p * (1 - p) ^ k)) :
    G = ProbabilityTheory.geometricMeasure
      (⟨p, ⟨le_of_lt hp0, hp1⟩⟩ : unitInterval.Elem) := by
  apply Measure.ext_of_singleton
  intro k
  rw [hGeom k]
  have hp : (⟨p, ⟨le_of_lt hp0, hp1⟩⟩ : unitInterval.Elem) ≠ 0 := by
    intro h
    have hpz : p = 0 := congrArg Subtype.val h
    exact (ne_of_gt hp0) hpz
  rw [ProbabilityTheory.geometricMeasure_singleton hp k]
  congr 1
  ring
