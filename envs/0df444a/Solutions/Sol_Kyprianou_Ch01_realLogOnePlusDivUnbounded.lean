-- Prove2me | solution 1 for Kyprianou.Ch01.realLogOnePlusDivUnbounded
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T13:01:43.726511+00:00
-- url     : https://prove2.me/submissions/d4b2905c-84be-47be-83c7-3c7c7b8c2be6

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Real
open scoped NNReal ENNReal
set_option autoImplicit false

/-- An explicit exponential time makes the harmonic logarithm arbitrarily large. -/
theorem solution
    (C : ℝ) (hC : 0 < C) (t : ℝ≥0) :
    ∃ s : ℝ≥0,
      (t : ℝ) < Real.log (1 + (s : ℝ)) / C := by
  let z : ℝ := C * (t : ℝ) + 1
  refine ⟨Real.toNNReal (Real.exp z), ?_⟩
  have hexp : 0 ≤ Real.exp z := le_of_lt (Real.exp_pos z)
  rw [Real.coe_toNNReal _ hexp]
  have harg : 0 < (1 : ℝ) + Real.exp z := by positivity
  have hlog : z < Real.log (1 + Real.exp z) := by
    apply (Real.lt_log_iff_exp_lt harg).2
    linarith
  apply (lt_div_iff₀ hC).2
  dsimp [z] at hlog
  linarith
