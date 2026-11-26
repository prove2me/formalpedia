-- Prove2me | solution 1 for Kyprianou.Ch04.cor412_finite_iff_negative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:20:11.223514+00:00
-- url     : https://prove2.me/submissions/84f99335-016a-43ec-a901-b9a89c9491c5

import Mathlib
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F) (w : Ω) :
    (Kyprianou.Ch03.firstHittingTime L.X (Iio 0) w ≠ ⊤) ↔
      ∃ t : NNReal, L.X t w < 0 := by
  constructor
  · intro h
    by_contra hn
    have hempty : {t : NNReal | 0 < t ∧ L.X t w ∈ Iio 0} = ∅ := by
      apply eq_empty_of_subset_empty
      intro t ht
      exact hn ⟨t, ht.2⟩
    apply h
    unfold Kyprianou.Ch03.firstHittingTime
    rw [hempty, image_empty, sInf_empty]
  · rintro ⟨t, ht⟩
    have hp : 0 < t := by
      by_contra hn
      have hz : t = 0 := le_antisymm (le_of_not_gt hn) (show 0 ≤ t from zero_le)
      simp [hz, L.X_zero w] at ht
    unfold Kyprianou.Ch03.firstHittingTime
    exact ne_of_lt (lt_of_le_of_lt
      (sInf_le ⟨t, ⟨hp, ht⟩, rfl⟩) (WithTop.coe_lt_top t))
