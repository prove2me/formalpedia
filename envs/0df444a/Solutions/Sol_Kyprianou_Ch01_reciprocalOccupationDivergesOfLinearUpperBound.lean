-- Prove2me | solution 1 for Kyprianou.Ch01.reciprocalOccupationDivergesOfLinearUpperBound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T12:39:52.014109+00:00
-- url     : https://prove2.me/submissions/38ac5854-31c9-4fb2-9f03-c3897f79d256

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Theorems.Thm_Kyprianou_Ch01_harmonicReciprocalLIntegralUnbounded
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Compare inverse-speed occupation to the divergent harmonic integral. -/
theorem solution
    {Ω : Type*} (X : ℝ≥0 → Ω → ℤ) (ω : Ω)
    (C : ℝ) (hC : 0 < C)
    (hUpper : ∀ t : ℝ≥0,
      (X t ω : ℝ) ≤ C * (1 + (t : ℝ))) :
    ∀ t : ℝ≥0, ∃ s : ℝ≥0,
      (t : ℝ≥0∞) < reciprocalOccupation X s ω := by
  intro t
  obtain ⟨s, hs⟩ :=
    Kyprianou.Ch01.harmonicReciprocalLIntegralUnbounded C hC t
  refine ⟨s, lt_of_lt_of_le hs ?_⟩
  unfold reciprocalOccupation
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
  have hr0 : 0 ≤ r := le_of_lt hr.1
  have hreal := hUpper (Real.toNNReal r)
  rw [Real.coe_toNNReal r hr0] at hreal
  have he : ENNReal.ofReal (X (Real.toNNReal r) ω : ℝ) ≤
      ENNReal.ofReal (C * (1 + r)) :=
    ENNReal.ofReal_le_ofReal hreal
  exact ENNReal.inv_le_inv' he
