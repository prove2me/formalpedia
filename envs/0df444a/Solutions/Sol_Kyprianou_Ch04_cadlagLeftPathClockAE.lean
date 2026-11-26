-- Prove2me | solution 1 for Kyprianou.Ch04.cadlagLeftPathClockAE
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T08:46:12.124023+00:00
-- url     : https://prove2.me/submissions/3abc7cfc-2865-4094-8f9d-f164b877bba3

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_cadlag_jump_time_set_countable_from_rational_grids
open MeasureTheory Filter Set Topology
open scoped NNReal
set_option autoImplicit false

/-- The path and its left limit agree at Lebesgue-almost every nonnegative real time. -/
theorem solution (Y L : NNReal → ℝ)
    (hr : ∀ t, ContinuousWithinAt Y (Ici t) t)
    (hl : ∀ t : NNReal, 0 < t → Tendsto Y (nhdsWithin t (Iio t)) (nhds (L t))) :
    ∀ᵐ s ∂volume.restrict (Ici (0 : ℝ)), Y s.toNNReal = L s.toNNReal := by
  have he (t : NNReal) (ht : 0 < t) : Function.leftLim Y t = L t := by
    haveI : (nhdsWithin t (Iio t)).NeBot := nhdsLT_neBot_of_exists_lt ⟨0,ht⟩
    exact leftLim_eq_of_tendsto (hl t ht)
  have hl' (t : NNReal) (ht : 0 < t) :
      Tendsto Y (nhdsWithin t (Iio t)) (nhds (Function.leftLim Y t)) := by
    rw [he t ht]
    exact hl t ht
  obtain ⟨pairs,hpairs⟩ := exists_surjective_nat (ℕ × ℚ)
  have hc := AvramDividend.Classical.avram_wave7_01_cadlag_jump_time_set_countable_from_rational_grids
    Y hr hl' (TopologicalSpace.denseSeq NNReal) (TopologicalSpace.denseRange_denseSeq NNReal)
    pairs hpairs
  let S := ((fun t : NNReal => (t : ℝ)) '' {t : NNReal |
      0 < t ∧ Y t - Function.leftLim Y t ≠ 0}) ∪ {0}
  have hS : S.Countable := (hc.image _).union (Set.countable_singleton 0)
  filter_upwards [ae_restrict_of_ae (hS.ae_notMem volume),
    ae_restrict_mem measurableSet_Ici] with s hs hnon
  have hs0 : s ≠ 0 := fun h => hs (Or.inr h)
  have hpos : 0 < s := lt_of_le_of_ne hnon (Ne.symm hs0)
  have ht : 0 < s.toNNReal := Real.toNNReal_pos.mpr hpos
  by_contra h
  apply hs
  exact Or.inl ⟨s.toNNReal,⟨ht,by rw [he _ ht]; exact sub_ne_zero.mpr h⟩,
    Real.coe_toNNReal _ hnon⟩
