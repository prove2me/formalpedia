-- Prove2me | solution 1 for Kyprianou.Ch01.harmonicReciprocalLIntegralUnbounded
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T13:02:36.053831+00:00
-- url     : https://prove2.me/submissions/65045ced-6577-4db2-91fd-bc2065199a4d

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Theorems.Thm_Kyprianou_Ch01_harmonicReciprocalLIntegralFormula
import Theorems.Thm_Kyprianou_Ch01_realLogOnePlusDivUnbounded
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Kyprianou.Ch01 Set Filter Real
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The extended harmonic integral exceeds every finite time. -/
theorem solution (C : ℝ) (hC : 0 < C) :
    ∀ t : ℝ≥0, ∃ s : ℝ≥0,
      (t : ℝ≥0∞) <
        (∫⁻ r in Set.Ioc (0 : ℝ) (s : ℝ),
          (ENNReal.ofReal (C * (1 + r)))⁻¹ ∂volume) := by
  intro t
  obtain ⟨s, hs⟩ :=
    Kyprianou.Ch01.realLogOnePlusDivUnbounded C hC t
  refine ⟨s, ?_⟩
  rw [Kyprianou.Ch01.harmonicReciprocalLIntegralFormula C hC s]
  have hp : 0 < Real.log (1 + (s : ℝ)) / C :=
    lt_of_le_of_lt (NNReal.coe_nonneg t) hs
  have hh : ENNReal.ofReal (t : ℝ) <
      ENNReal.ofReal (Real.log (1 + (s : ℝ)) / C) :=
    (ENNReal.ofReal_lt_ofReal_iff hp).2 hs
  simpa using hh
