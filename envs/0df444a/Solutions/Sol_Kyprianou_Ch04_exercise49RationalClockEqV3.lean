-- Prove2me | solution 1 for Kyprianou.Ch04.exercise49RationalClockEqV3
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:44:43.698719+00:00
-- url     : https://prove2.me/submissions/173d80b7-fc31-431b-9b59-f887c04458d7

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_openHitLtRationalWitness
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false
/-- For a right-continuous real path nonnegative at zero, strict first passage equals its rational infimum. -/
theorem solution
    (Y : NNReal → ℝ) (h0 : 0 ≤ Y 0)
    (hrc : ∀ t : NNReal, ContinuousWithinAt Y (Ici t) t) :
    (sInf {v : WithTop NNReal | ∃ t : NNReal,
      v = ↑t ∧ 0 < t ∧ Y t < 0}) =
      ⨅ q : ℚ, if 0 < (q : ℝ) ∧ Y (Real.toNNReal q) < 0 then
        (↑(Real.toNNReal q) : WithTop NNReal) else ⊤ := by
  classical
  let C : WithTop NNReal := ⨅ q : ℚ,
    if 0 < (q : ℝ) ∧ Y (Real.toNNReal q) < 0 then
      (↑(Real.toNNReal q) : WithTop NNReal) else ⊤
  change _ = C
  apply le_antisymm
  · apply le_iInf
    intro q
    split
    · rename_i h
      exact sInf_le ⟨Real.toNNReal q, rfl, Real.toNNReal_pos.mpr h.1, h.2⟩
    · exact le_top
  · by_contra! hn
    obtain ⟨v, hv, hv'⟩ := exists_between hn
    cases v with
    | top => exact (not_lt_of_ge le_top) hv'
    | coe c =>
      have hS : {v : WithTop NNReal |
          ∃ t : NNReal, v = ↑t ∧ 0 < t ∧ Y t < 0} =
          {v : WithTop NNReal | ∃ t : NNReal, v = ↑t ∧ Y t ∈ Iio 0} := by
        ext v
        constructor
        · rintro ⟨t, rfl, _, ht⟩
          exact ⟨t, rfl, ht⟩
        · rintro ⟨t, rfl, ht⟩
          refine ⟨t, rfl, ?_, ht⟩
          by_contra h
          have ht0 : t = 0 := le_antisymm (le_of_not_gt h) bot_le
          exact (not_lt_of_ge h0) (ht0 ▸ ht)
      rw [hS] at hv
      obtain ⟨q, hq, hqc, hneg⟩ :=
        (Kyprianou.Ch04.openHitLtRationalWitness
          Y (Iio 0) isOpen_Iio hrc c).mp hv
      have hq' : 0 < (q : ℝ) := by exact_mod_cast hq
      have hb : C ≤ (↑(Real.toNNReal q) : WithTop NNReal) := by
        unfold C
        exact le_trans (iInf_le _ q) (by rw [if_pos ⟨hq', hneg⟩])
      have hc : (↑(Real.toNNReal q) : WithTop NNReal) < ↑c :=
        WithTop.coe_lt_coe.mpr ((Real.toNNReal_lt_iff_lt_coe hq'.le).2 hqc)
      exact (not_lt_of_ge hb) (hc.trans hv')
