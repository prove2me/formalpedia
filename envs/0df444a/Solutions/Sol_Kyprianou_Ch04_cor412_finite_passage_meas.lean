-- Prove2me | solution 1 for Kyprianou.Ch04.cor412_finite_passage_meas
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T08:42:07.998952+00:00
-- url     : https://prove2.me/submissions/8570bf1c-f32f-438a-a131-9b844ace4faf

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Theorems.Thm_Kyprianou_Ch04_cor412_lower_stop
import Theorems.Thm_Kyprianou_Ch04_cor412_finite_cap_union
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The finite passage event is measurable. -/
theorem solution {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F) :
    MeasurableSet {w | Kyprianou.Ch03.firstHittingTime L.X (Iio 0) w ≠ ⊤} := by
  let τ : Ω → WithTop NNReal := fun w => Kyprianou.Ch03.firstHittingTime L.X (Iio 0) w
  change MeasurableSet {w | τ w ≠ ⊤}
  rw [← Kyprianou.Ch04.cor412_finite_cap_union τ]
  exact MeasurableSet.iUnion fun n =>
    (F.rightCont.le (n : NNReal)) _ ((Kyprianou.Ch04.cor412_lower_stop P F L) (n : NNReal))
