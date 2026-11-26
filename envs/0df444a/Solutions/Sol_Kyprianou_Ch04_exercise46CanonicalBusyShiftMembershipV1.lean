-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46CanonicalBusyShiftMembershipV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:28:26.66137+00:00
-- url     : https://prove2.me/submissions/deeeacb6-427b-4ddf-893a-13369344ac7f

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise46RecordShiftDrawdownV1
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_shifted_future_source_leftLim_translation
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (G : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : SpectrallyNegativeLevy P G) (w : Omega) (s u : NNReal) (hu : 0 < u)
    (hrecord : ∀ v ≤ s, L.X v w ≤ L.X s w)
    (hb : BddAbove ((fun t : NNReal => L.X t w) '' Iic (s+u))) :
    let Y : NNReal → Real := fun t => L.X (s+t) w - L.X s w
    (0 < s+u ∧ 0 < sSup ((fun t : NNReal => L.X t w) '' Iic (s+u)) - L.X (s+u) w ∧
      sSup ((fun t : NNReal => L.X t w) '' Iic (s+u)) - L.X (s+u) w =
        -(L.X (s+u) w - Function.leftLim (fun t : NNReal => L.X t w) (s+u))) ↔
    (0 < u ∧ 0 < sSup (Y '' Iic u) - Y u ∧
      sSup (Y '' Iic u) - Y u = -(Y u - Function.leftLim Y u)) := by
  dsimp only
  rw [Kyprianou.Ch04.exercise46RecordShiftDrawdownV1 (fun t => L.X t w) s u hrecord hb,
    avram_wave5_01_actual_shifted_future_source_leftLim_translation L w s u hu]
  have hpos : 0 < s+u := lt_of_lt_of_le hu (le_add_left (le_refl u))
  have he : L.X (s+u) w - L.X s w -
      (Function.leftLim (fun t : NNReal => L.X t w) (s+u) - L.X s w) =
      L.X (s+u) w - Function.leftLim (fun t : NNReal => L.X t w) (s+u) := by ring
  rw [he]
  simp [hu,hpos]
