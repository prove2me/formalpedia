-- Prove2me | solution 1 for Kyprianou.Ch04.exercise49GlobalLowerBoundRationalV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:55:51.658802+00:00
-- url     : https://prove2.me/submissions/2ca63538-8cb1-468b-baae-aec7d2832cba

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_openHitLtRationalWitness
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false
/-- A cadlag path lower bound on the entire half-line is equivalent to its positive rational samples. -/
theorem solution
    (Y : NNReal → ℝ) (hr : ∀ t, ContinuousWithinAt Y (Ici t) t)
    (b : ℝ) :
    (∀ u : NNReal, b ≤ Y u) ↔
      ∀ q : ℚ, 0 < q → b ≤ Y (Real.toNNReal q) := by
  constructor
  · intro h q _
    exact h _
  · intro h u
    by_contra! hn
    have hh : sInf {v : WithTop NNReal |
        ∃ t : NNReal, v = ↑t ∧ Y t ∈ Iio b} <
          ((u + 1 : NNReal) : WithTop NNReal) :=
      lt_of_le_of_lt (sInf_le ⟨u, rfl, hn⟩) (WithTop.coe_lt_coe.mpr (by simp))
    obtain ⟨q, hq0, _, hneg⟩ :=
      (Kyprianou.Ch04.openHitLtRationalWitness
        Y (Iio b) isOpen_Iio hr (u + 1)).mp hh
    exact (not_lt_of_ge (h q hq0)) hneg
