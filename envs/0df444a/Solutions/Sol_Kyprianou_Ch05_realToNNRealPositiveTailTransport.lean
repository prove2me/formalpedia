-- Prove2me | solution 1 for Kyprianou.Ch05.realToNNRealPositiveTailTransport
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T20:21:45.848149+00:00
-- url     : https://prove2.me/submissions/28a2cbe9-3993-4cdc-ac78-3275b380bc3b

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_RenewalEpochProcess
open MeasureTheory Filter Set ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

/-- Positive upper rays and first moment transport under the nonnegative-part map. -/
theorem solution
    (F : Measure Real) [IsProbabilityMeasure F]
    (hInt : Integrable (fun z : Real => z) F) :
    let m := Measure.map Real.toNNReal F
    (∫⁻ z : ℝ≥0, ENNReal.ofReal (z : ℝ) ∂m) < ⊤ ∧
      ∀ t : Real, 0 < t → m {z : ℝ≥0 | t < (z : ℝ)} = F (Ioi t) := by
  let m := Measure.map Real.toNNReal F
  have hm : Measurable Real.toNNReal := measurable_id.real_toNNReal
  refine ⟨?_,?_⟩
  · rw [lintegral_map (f := fun z : ℝ≥0 => ENNReal.ofReal (z : ℝ))
      (ENNReal.measurable_ofReal.comp measurable_coe_nnreal_real) hm]
    refine lt_of_le_of_lt (lintegral_mono ?_) ((hasFiniteIntegral_iff_norm _).mp hInt.hasFiniteIntegral)
    intro t
    apply ENNReal.ofReal_le_ofReal
    by_cases ht : 0 ≤ t
    · rw [Real.coe_toNNReal t ht, Real.norm_eq_abs, abs_of_nonneg ht]
    · rw [Real.toNNReal_of_nonpos (le_of_not_ge ht)]
      simpa using abs_nonneg t
  · intro t ht
    rw [Measure.map_apply hm (measurableSet_lt measurable_const measurable_coe_nnreal_real)]
    congr 1
    ext z
    change (t < (z.toNNReal : ℝ)) ↔ t < z
    by_cases hz : 0 ≤ z
    · rw [Real.coe_toNNReal z hz]
    · rw [Real.toNNReal_of_nonpos (le_of_not_ge hz)]
      simp only [NNReal.coe_zero]
      exact iff_of_false (not_lt_of_ge ht.le) (by linarith)
