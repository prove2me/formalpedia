-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41PrezeroProductNullV6
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T10:42:21.892279+00:00
-- url     : https://prove2.me/submissions/d061e907-dc09-422d-bd1a-d111bad499c6

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise41PredictableZeroSetV6
import Theorems.Thm_Kyprianou_Ch04_exercise41MappedTimeCountableNullV6
import Theorems.Thm_Kyprianou_Ch04_exercise41LeftZeroCountableV6
import Theorems.Thm_Kyprianou_Ch04_exercise41ZeroVisitsLocallyFiniteV1
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical
set_option autoImplicit false
open Kyprianou.Ch04
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation) (hd : 0 < L.drift) (T : NNReal) :
    let E : Set (NNReal × Ω) := {p | 0 < p.1 ∧ p.1 ≤ T ∧
      Function.leftLim (fun t => L.X t p.2) p.1 = 0}
    ((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) E = 0 := by
  letI : IsProbabilityMeasure P := L.isProbability
  let μ := ((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal
  letI : IsFiniteMeasure ((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))) :=
    isFiniteMeasure_restrict.mpr (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  letI : IsFiniteMeasure μ := Measure.isFiniteMeasure_map _ _
  let E : Set (NNReal × Ω) := {p | 0 < p.1 ∧ p.1 ≤ T ∧
    Function.leftLim (fun t => L.X t p.2) p.1 = 0}
  have he : MeasurableSet E := (exercise41PredictableZeroSetV6 P F L T).2
  change μ.prod P E = 0
  rw [Measure.prod_apply_symm he]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [exercise41ZeroVisitsLocallyFiniteV1 P F L hBV hd] with w hw
  exact exercise41MappedTimeCountableNullV6 T _
    (exercise41LeftZeroCountableV6 (fun t => L.X t w) T
      (L.rightCont w) (L.leftLim w) (hw T))
