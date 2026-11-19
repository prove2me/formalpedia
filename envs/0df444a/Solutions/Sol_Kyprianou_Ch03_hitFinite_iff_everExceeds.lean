-- Prove2me | solution 1 for Kyprianou.Ch03.hitFinite_iff_everExceeds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T18:46:19.060462+00:00
-- url     : https://prove2.me/submissions/b3683a38-fe24-438f-9278-795c0c6273f6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_LevyExtrema_SBA_runSup
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

open Kyprianou.Ch03

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (x : ℝ) (hx : 0 ≤ x) (omega : Omega) :
    (∃ t : NNReal, x < L.X t omega) ↔
      (firstHittingTime L.X (Set.Ioi x) omega != ⊤) := by
  refine Iff.intro ?_ ?_
  · rintro ⟨t, ht⟩
    have hposTime : 0 < t := by
      by_contra hnonpos
      have htzero : t = 0 :=
        le_antisymm (le_of_not_gt hnonpos) (show (0 : NNReal) ≤ t from zero_le)
      have hzeroTime : L.X t omega = 0 := by
        simpa [htzero] using (L.X_zero omega)
      linarith
    have hle :
        sInf ((fun s : NNReal => (s : WithTop NNReal)) ''
          {s : NNReal | 0 < s ∧ L.X s omega ∈ Set.Ioi x}) ≤
            (t : WithTop NNReal) :=
      sInf_le ⟨t, ⟨hposTime, ht⟩, rfl⟩
    have hlt : firstHittingTime L.X (Set.Ioi x) omega < ⊤ := by
      unfold firstHittingTime
      exact lt_of_le_of_lt hle (WithTop.coe_lt_top t)
    have hne : firstHittingTime L.X (Set.Ioi x) omega ≠ ⊤ :=
      ne_of_lt hlt
    simpa [hne]
  · refine fun ht => ?_
    by_contra hNo
    have hEmpty :
        {s : NNReal | 0 < s ∧ L.X s omega ∈ Set.Ioi x} =
          ∅ := by
      apply Set.eq_empty_of_subset_empty
      intro s hs
      exact hNo ⟨s, hs.2⟩
    have htop : firstHittingTime L.X (Set.Ioi x) omega = ⊤ := by
      unfold firstHittingTime
      rw [hEmpty]
      simp
      intro a ha
      rcases ha with ⟨u, hu, _⟩
      simp at hu
    simp [htop] at ht

