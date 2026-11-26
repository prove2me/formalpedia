-- Prove2me | solution 1 for Kyprianou.Ch05.renewalResolventScalarIdentity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T17:20:40.557894+00:00
-- url     : https://prove2.me/submissions/6ef685bb-9cf7-4aee-8c88-92cfc19ba43e

import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Probability.ConditionalProbability
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

/-- For a strictly positive exponent a, the geometric reciprocal of the unit-discount resolvent equals one plus the undiscounted resolvent. -/
theorem solution
    (a : Real) (ha : 0 < a) :
    (1 - (ENNReal.ofReal (1 + a))⁻¹)⁻¹ =
      1 + (ENNReal.ofReal a)⁻¹ := by
  have hp : 0 < 1 + a := by linarith
  have hr : 0 < 1 - (1 + a)⁻¹ := by
    rw [sub_pos, inv_lt_one_iff₀]
    right
    linarith
  rw [← ENNReal.ofReal_inv_of_pos hp, ← ENNReal.ofReal_one,
    ← ENNReal.ofReal_sub 1 (inv_nonneg.mpr hp.le),
    ← ENNReal.ofReal_inv_of_pos hr, ← ENNReal.ofReal_inv_of_pos ha,
    ← ENNReal.ofReal_add zero_le_one (inv_nonneg.mpr ha.le)]
  congr 1
  field_simp [ne_of_gt ha, ne_of_gt hp, ne_of_gt hr] <;> ring
