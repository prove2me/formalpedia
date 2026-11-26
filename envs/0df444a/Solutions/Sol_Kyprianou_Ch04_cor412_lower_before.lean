-- Prove2me | solution 1 for Kyprianou.Ch04.cor412_lower_before
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T08:08:25.369487+00:00
-- url     : https://prove2.me/submissions/752e0b3d-7d6f-45df-887d-9d02a534d2ca

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

/-- Before a finite negative hitting clock the path is nonnegative. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F) (w : Ω) (t : NNReal)
    (ht : Kyprianou.Ch03.firstHittingTime L.X (Iio 0) w = (t : WithTop NNReal)) :
    ∀ s : NNReal, s < t → 0 ≤ L.X s w := by
  intro s hs
  by_contra hn
  have hx : L.X s w < 0 := lt_of_not_ge hn
  have hp : 0 < s := by
    by_contra h
    have hz : s = 0 := le_antisymm (le_of_not_gt h) zero_le
    simp [hz,L.X_zero] at hx
  have hle : Kyprianou.Ch03.firstHittingTime L.X (Iio 0) w ≤ (s : WithTop NNReal) := by
    unfold Kyprianou.Ch03.firstHittingTime
    exact sInf_le ⟨s,⟨hp,hx⟩,rfl⟩
  rw [ht] at hle
  exact (not_le_of_gt hs) (WithTop.coe_le_coe.mp hle)
