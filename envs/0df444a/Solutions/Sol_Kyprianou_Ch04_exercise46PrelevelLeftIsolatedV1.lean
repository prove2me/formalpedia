-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46PrelevelLeftIsolatedV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:15:06.378507+00:00
-- url     : https://prove2.me/submissions/d9691bc3-e091-465d-9221-982ba364af3c

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise46LeftIsolatedCountableV1
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    (f : NNReal → Real) (x : Real)
    (hAffine : ∀ t : NNReal, 0 < t →
      ∃ s : NNReal, s < t ∧ ∀ u : NNReal, s < u → u ≤ t →
        Function.leftLim f u = f s + ((u : Real) - (s : Real))) :
    ({t : NNReal | 0 < t ∧ Function.leftLim f t = x}).Countable := by
  apply Kyprianou.Ch04.exercise46LeftIsolatedCountableV1
  intro t ht
  obtain ⟨s, hst, hs⟩ := hAffine t ht.1
  refine ⟨s, hst, ?_⟩
  intro u hu hsu hut
  have h1 := hs u hsu hut.le
  have h2 := hs t hst le_rfl
  rw [hu.2] at h1
  rw [ht.2] at h2
  have he : (u : Real) = (t : Real) := by linarith
  exact (ne_of_lt hut) (NNReal.eq he)
