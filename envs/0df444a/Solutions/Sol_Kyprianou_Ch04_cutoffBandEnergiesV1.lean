-- Prove2me | solution 1 for Kyprianou.Ch04.cutoffBandEnergiesV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T00:00:59.516342+00:00
-- url     : https://prove2.me/submissions/ca0ad1bf-d4b4-4e99-aa4a-fd49ef9cfb36

import Mathlib
import Definitions.Def_LeanLevy_Levy_LevyMeasure
import Theorems.Thm_Kyprianou_Ch04_integratedKernelBudgetV1
import Theorems.Thm_Kyprianou_Ch04_levyBandEnergyV1
import Theorems.Thm_Kyprianou_Ch04_cutoffPredictableIntegrandSquareBoundV1
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Integrability and exact quadratic bounds for the two nested cutoff bands. -/
theorem solution (ν : Measure ℝ) (hν : IsLevyMeasure ν)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (hb : b < 1) :
    let A : Set ℝ := {z | a < |z| ∧ |z| ≤ b ∧ |z| < 1}
    let B : Set ℝ := {z | b < |z| ∧ |z| < 1}
    let C : Set ℝ := {z | |z| ≤ b}
    let D : Set ℝ := {z | |z| < 1}
    (Integrable (A.indicator (fun z => z^2)) ν ∧
      0 ≤ ∫ z, A.indicator (fun z => z^2) z ∂ν ∧
      (∫ z, A.indicator (fun z => z^2) z ∂ν) ≤
        (∫⁻ z in C, ENNReal.ofReal (z^2) ∂ν).toReal) ∧
    (Integrable (B.indicator (fun z => z^2)) ν ∧
      0 ≤ ∫ z, B.indicator (fun z => z^2) z ∂ν ∧
      (∫ z, B.indicator (fun z => z^2) z ∂ν) ≤
        (∫⁻ z in D, ENNReal.ofReal (z^2) ∂ν).toReal) := by
  let A : Set ℝ := {z | a < |z| ∧ |z| ≤ b ∧ |z| < 1}
  let B : Set ℝ := {z | b < |z| ∧ |z| < 1}
  let C : Set ℝ := {z | |z| ≤ b}
  let D : Set ℝ := {z | |z| < 1}
  have hA : MeasurableSet A := (measurableSet_lt measurable_const measurable_id.abs).inter
    ((measurableSet_le measurable_id.abs measurable_const).inter
      (measurableSet_lt measurable_id.abs measurable_const))
  have hB : MeasurableSet B := (measurableSet_lt measurable_const measurable_id.abs).inter
    (measurableSet_lt measurable_id.abs measurable_const)
  have hC : MeasurableSet C := measurableSet_le measurable_id.abs measurable_const
  have hDset : MeasurableSet D := measurableSet_lt measurable_id.abs measurable_const
  have hAfin : ν A < ⊤ := (measure_mono (show A ⊆ {z | a ≤ |z|} from
    fun z hz => hz.1.le)).trans_lt (hν.measure_setOf_abs_ge_lt_top ha)
  have hBfin : ν B < ⊤ := (measure_mono (show B ⊆ {z | b ≤ |z|} from
    fun z hz => hz.1.le)).trans_lt (hν.measure_setOf_abs_ge_lt_top (ha.trans hab))
  have hAb := Kyprianou.Ch04.levyBandEnergyV1 ν hν A C hA hC hAfin
    (fun z hz => hz.2.1) (fun z hz => hz.trans hb.le)
  have hBb := Kyprianou.Ch04.levyBandEnergyV1 ν hν B D hB hDset hBfin
    (fun z hz => hz.2) (fun z hz => hz.le)
  exact ⟨hAb,hBb⟩
