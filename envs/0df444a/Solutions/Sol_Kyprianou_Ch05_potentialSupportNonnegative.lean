-- Prove2me | solution 1 for Kyprianou.Ch05.potentialSupportNonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:56:25.293045+00:00
-- url     : https://prove2.me/submissions/e34b3fdf-9627-4b43-b27c-e2a724656ffb

import Mathlib
import Theorems.Thm_Kyprianou_Ch02_levyCoordinateAEMeasurableV1
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Set
open Kyprianou.Ch05
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (U : Real → Measure Real)
    (hKilled : IsKilledSubordinator P Y death 0)
    (hPotential : IsKilledPotentialFamily P Y death U) :
    (U 0) (Set.Iio (0 : Real)) = 0 := by
  have hM := Kyprianou.Ch02.levyCoordinateAEMeasurableV1 P Y hKilled.1.1
  rw [(hPotential 0 le_rfl).2 _ measurableSet_Iio]
  have hzero (t : Real) :
      P {w | (Real.toNNReal t : WithTop NNReal) < death w ∧
        Y (Real.toNNReal t) w ∈ Set.Iio (0 : Real)} = 0 := by
    have hn : ∀ᵐ w ∂P, 0 ≤ Y (Real.toNNReal t) w := by
      filter_upwards [hKilled.1.2] with w hw
      have hh := hw (show (0 : NNReal) ≤ Real.toNNReal t from zero_le)
      simpa [congrFun hKilled.1.1.start_zero w] using hh
    have hz : (P.map (Y (Real.toNNReal t))) (Set.Iio (0 : Real)) = 0 := by
      rw [Measure.map_apply_of_aemeasurable (hM _) measurableSet_Iio]
      have he : Y (Real.toNNReal t) ⁻¹' Set.Iio (0 : Real) =
          {w | ¬ 0 ≤ Y (Real.toNNReal t) w} := by
        ext w
        simp [not_le]
      rw [he]
      exact ae_iff.mp hn
    rw [Measure.map_apply_of_aemeasurable (hM _) measurableSet_Iio] at hz
    exact measure_mono_null (fun w hw => hw.2) hz
  simp_rw [hzero,mul_zero]
  simp
