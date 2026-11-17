-- Prove2me | solution 1 for Kyprianou.Ch01.logarithmicJumpPMFExists
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T00:08:29.129863+00:00
-- url     : https://prove2.me/submissions/256766a0-b8a6-4325-89e9-bbe570d13399

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_logarithmicJumpWeightsENNRealMass
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
set_option autoImplicit false

/-! The logarithmic jump weights define a genuine probability mass function. -/
theorem solution
    (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    ∃ jump : PMF ℕ, ∀ n : ℕ,
      jump n = ENNReal.ofReal
        ((q ^ (n + 1) / ((n : ℝ) + 1)) / (-Real.log (1 - q))) := by
  refine ⟨⟨fun n : ℕ =>
    ENNReal.ofReal
      ((q ^ (n + 1) / ((n : ℝ) + 1)) / (-Real.log (1 - q))),
    (ENNReal.summable).hasSum_iff.mpr
      (Kyprianou.Ch01.logarithmicJumpWeightsENNRealMass q hq0 hq1)⟩, ?_⟩
  intro n
  rfl
