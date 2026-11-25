-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46CDFWithoutZeroAtomV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T10:19:47.109913+00:00
-- url     : https://prove2.me/submissions/891ef119-7f33-4cc2-aded-a51795cfb74f

import Mathlib
open MeasureTheory Set
open scoped ENNReal
set_option autoImplicit false
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (I : Omega → ENNReal) (hm : Measurable I)
    (hz : (P {omega | I omega = 0}).toReal = 0)
    (a : ENNReal) :
    (P {omega | I omega ≤ a}).toReal =
      (P {omega | 0 < I omega ∧ I omega ≤ a}).toReal := by
  let A : Set Omega := {omega | 0 < I omega ∧ I omega ≤ a}
  let B : Set Omega := {omega | I omega = 0}
  have hB : MeasurableSet B := hm measurableSet_eq
  have hdis : Disjoint A B := by
    refine Set.disjoint_left.mpr ?_
    intro omega ha hb
    exact (ne_of_gt ha.1) hb
  have hu : {omega | I omega ≤ a} = A ∪ B := by
    ext omega
    constructor
    · intro hle
      by_cases hz' : I omega = 0
      · exact Or.inr hz'
      · exact Or.inl ⟨pos_iff_ne_zero.mpr hz', hle⟩
    · rintro (ha | hb)
      · exact ha.2
      · change I omega = 0 at hb
        simp [hb]
  rw [hu, measure_union hdis hB, ENNReal.toReal_add
    (measure_ne_top P A) (measure_ne_top P B)]
  change (P A).toReal + (P {omega | I omega = 0}).toReal = _
  rw [hz, add_zero]
