-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46WeakPassageSandwichV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T21:24:53.854645+00:00
-- url     : https://prove2.me/submissions/2b3cc738-3179-4970-a5a6-7f295056fedb

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Pathwise weak busy clock lies between strict passage clocks at neighbouring levels. -/
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (G : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : SpectrallyNegativeLevy P G)
    (x y : Real) (hxy : x < y) (w : Omega) :
    let B : WithTop NNReal :=
      sInf {v : WithTop NNReal |
        ∃ t : NNReal, v = ↑t ∧ 0 < t ∧ y ≤ L.X t w}
    Kyprianou.Ch03.firstHittingTime L.X (Ioi x) w ≤ B ∧
      B ≤ Kyprianou.Ch03.firstHittingTime L.X (Ioi y) w := by
  dsimp only
  unfold Kyprianou.Ch03.firstHittingTime
  constructor
  · apply sInf_le_sInf
    rintro v ⟨t, rfl, ht, hy⟩
    exact ⟨t, ⟨ht, hxy.trans_le hy⟩, rfl⟩
  · apply sInf_le_sInf
    rintro v ⟨t, ⟨ht, hy⟩, rfl⟩
    exact ⟨t, rfl, ht, hy.le⟩
