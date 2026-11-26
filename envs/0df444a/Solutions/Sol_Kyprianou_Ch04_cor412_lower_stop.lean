-- Prove2me | solution 1 for Kyprianou.Ch04.cor412_lower_stop
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T08:08:25.244941+00:00
-- url     : https://prove2.me/submissions/a2e600e3-dca5-4c6c-ad03-738ab7f74c53

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Theorems.Thm_AvramDividend_Classical_levy_lowerCrossing_before_filtration_measurable
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

/-- The strict negative hitting time is a stopping time in the right-continuous filtration. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F) :
    IsStoppingTime F.rightCont
      (fun w => Kyprianou.Ch03.firstHittingTime L.X (Iio 0) w) := by
  apply isStoppingTime_of_measurableSet_lt_of_isRightContinuous
  intro t
  have heq :
      {w : Ω | Kyprianou.Ch03.firstHittingTime L.X (Iio 0) w < (t : WithTop NNReal)} =
        {w : Ω | ∃ s : NNReal, s < t ∧ L.X s w < 0} := by
    ext w
    change sInf ((fun s : NNReal => (s : WithTop NNReal)) ''
      {s : NNReal | 0 < s ∧ L.X s w ∈ Iio 0}) < (t : WithTop NNReal) ↔ _
    rw [sInf_lt_iff]
    constructor
    · rintro ⟨a,⟨s,hs,rfl⟩,ha⟩
      exact ⟨s, WithTop.coe_lt_coe.mp ha, hs.2⟩
    · rintro ⟨s,hs,hx⟩
      have hp : 0 < s := by
        by_contra h
        have hz : s = 0 := le_antisymm (le_of_not_gt h) zero_le
        simp [hz,L.X_zero] at hx
      exact ⟨(s : WithTop NNReal),⟨s,⟨hp,hx⟩,rfl⟩,WithTop.coe_lt_coe.mpr hs⟩
  rw [heq]
  exact (F.le_rightCont t) _ (levy_lowerCrossing_before_filtration_measurable L 0 t)
