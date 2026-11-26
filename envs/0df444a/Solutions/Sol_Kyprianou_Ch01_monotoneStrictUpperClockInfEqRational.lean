-- Prove2me | solution 1 for Kyprianou.Ch01.monotoneStrictUpperClockInfEqRational
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T02:32:42.794866+00:00
-- url     : https://prove2.me/submissions/dc2a3a37-6dff-43be-9818-db44b49da99f

import Mathlib
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false
theorem _root_.solution
    (f : ℝ≥0 → ℝ≥0∞) (hmono : Monotone f) (a : ℝ≥0∞) :
    (sInf {z : WithTop ℝ≥0 |
      ∃ u : ℝ≥0, (u : WithTop ℝ≥0) = z ∧ a < f u}) =
      ⨅ r : ℚ,
        if a < f (Real.toNNReal (r : ℝ)) then
          ((Real.toNNReal (r : ℝ) : ℝ≥0) : WithTop ℝ≥0)
        else ⊤ := by
  apply le_antisymm
  · refine le_iInf fun r => ?_
    split
    · rename_i h
      exact sInf_le ⟨_, rfl, h⟩
    · exact le_top
  · refine le_sInf ?_
    rintro z ⟨u, rfl, hu⟩
    refine le_of_forall_gt_imp_ge_of_dense fun w hw => ?_
    induction w using WithTop.recTopCoe with
    | top => exact le_top
    | coe w =>
      have huw : (u : ℝ) < (w : ℝ) := by exact_mod_cast hw
      obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn huw
      have h1 : u ≤ Real.toNNReal (r : ℝ) := by
        rw [Real.le_toNNReal_iff_coe_le (le_of_lt (lt_of_le_of_lt u.coe_nonneg hr1))]
        exact hr1.le
      have h2 : Real.toNNReal (r : ℝ) ≤ w := by
        rw [Real.toNNReal_le_iff_le_coe]; exact hr2.le
      refine iInf_le_of_le r ?_
      rw [if_pos (lt_of_lt_of_le hu (hmono h1))]
      exact_mod_cast h2

