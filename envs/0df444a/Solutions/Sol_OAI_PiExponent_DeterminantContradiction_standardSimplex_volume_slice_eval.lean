-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.standardSimplex_volume_slice_eval
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T11:56:40.909623+00:00
-- url     : https://prove2.me/submissions/8cb7d623-46bb-40cc-8f2d-2e1ab57bd101

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open scoped BigOperators

theorem solution (n : Nat) (T : Real) (hT : 0 < T)
    (ih : ∀ s : Real, 0 < s →
      MeasureTheory.volume
          {y : Fin n → Real | (∀ i, 0 ≤ y i) ∧ (∑ i, y i) < s} =
        ENNReal.ofReal (s ^ n / (n.factorial : Real))) :
    (∫⁻ t in Set.Ioo (0 : Real) T,
        MeasureTheory.volume
          {y : Fin n → Real | (∀ i, 0 ≤ y i) ∧ (∑ i, y i) < T - t}
          ∂MeasureTheory.volume) =
      (∫⁻ t in Set.Ioo (0 : Real) T,
        ENNReal.ofReal ((T - t) ^ n / (n.factorial : Real))
          ∂MeasureTheory.volume) := by
  apply MeasureTheory.lintegral_congr_ae
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
  exact ih (T - t) (sub_pos.mpr ht.2)