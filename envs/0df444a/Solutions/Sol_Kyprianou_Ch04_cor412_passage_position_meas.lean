-- Prove2me | solution 1 for Kyprianou.Ch04.cor412_passage_position_meas
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T09:40:11.147402+00:00
-- url     : https://prove2.me/submissions/5120426c-03fe-4b97-8c91-d4333904d4cd

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Theorems.Thm_Kyprianou_Ch04_cor412_lower_stop
import Theorems.Thm_Kyprianou_Ch04_cor412_finite_passage_meas
import Theorems.Thm_AvramDividend_Classical_tauceti_original_levy_stronglyProgressive
import Theorems.Thm_AvramDividend_Classical_levy_rightCont_process
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The arbitrary finite-time representative gives a measurable passage position under the restricted measure. -/
theorem solution {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F) (finiteTime : Ω → NNReal)
    (hfin : ∀ w, Kyprianou.Ch03.firstHittingTime L.X (Iio 0) w ≠ ⊤ →
      Kyprianou.Ch03.firstHittingTime L.X (Iio 0) w = (finiteTime w : WithTop NNReal)) :
    AEMeasurable (fun w => L.X (finiteTime w) w)
      (P.restrict {w | Kyprianou.Ch03.firstHittingTime L.X (Iio 0) w ≠ ⊤}) := by
  let τ : Ω → WithTop NNReal := fun w => Kyprianou.Ch03.firstHittingTime L.X (Iio 0) w
  let A : Set Ω := {w | τ w ≠ ⊤}
  have ht := Kyprianou.Ch04.cor412_lower_stop P F L
  have hp : IsStronglyProgressive F.rightCont L.X := by
    obtain ⟨Y,hY,_,_,_⟩ := levy_rightCont_process L
    simpa only [hY] using tauceti_original_levy_stronglyProgressive Y
  have hm : Measurable (stoppedValue L.X τ) :=
    (measurable_stoppedValue hp ht).mono ht.measurableSpace_le le_rfl
  have hA : MeasurableSet A := Kyprianou.Ch04.cor412_finite_passage_meas L
  apply hm.aemeasurable.congr
  filter_upwards [ae_restrict_mem (μ := P) hA] with w hw
  have he := hfin w hw
  unfold stoppedValue
  change L.X (τ w).untopA w = _
  change τ w = (finiteTime w : WithTop NNReal) at he
  rw [he, WithTop.untopA_eq_untop WithTop.coe_ne_top]
  rfl
