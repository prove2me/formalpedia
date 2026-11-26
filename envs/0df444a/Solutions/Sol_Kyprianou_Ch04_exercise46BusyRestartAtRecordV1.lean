-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46BusyRestartAtRecordV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:36:11.867912+00:00
-- url     : https://prove2.me/submissions/4977af18-8863-4f86-9e05-432fe1ab5bf1

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise46RecordShiftDrawdownV1
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_shifted_future_source_leftLim_translation
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (G : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : SpectrallyNegativeLevy P G)
    (w : Omega) (b u : NNReal) (hu : 0 < u)
    (hrecord : ∀ t ≤ b, L.X t w ≤ L.X b w)
    (hb : BddAbove ((fun t : NNReal => L.X t w) '' Iic (b+u))) :
    let f : NNReal → Real := fun t => L.X t w
    let g : NNReal → Real := fun t => f (b+t) - f b
    (0 < b+u ∧ sSup (f '' Iic (b+u)) = Function.leftLim f (b+u) ∧
      f (b+u) < Function.leftLim f (b+u)) ↔
    (0 < u ∧ sSup (g '' Iic u) = Function.leftLim g u ∧
      g u < Function.leftLim g u) := by
  dsimp only
  have hD := Kyprianou.Ch04.exercise46RecordShiftDrawdownV1
    (fun t : NNReal => L.X t w) b u hrecord hb
  have hL := avram_wave5_01_actual_shifted_future_source_leftLim_translation L w b u hu
  rw [hL]
  have hpos : 0 < b+u := by positivity
  simp only [hpos, hu, true_and, sub_lt_sub_iff_right]
  exact and_congr_left fun _ => ⟨fun h => by linarith [hD], fun h => by linarith [hD]⟩
