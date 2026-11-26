-- Prove2me | solution 1 for Kyprianou.Ch04.rationalNearRightPointV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:44:58.481935+00:00
-- url     : https://prove2.me/submissions/eee15d5d-c599-4d5e-a807-a5b191b1bfb4

import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Topology.Instances.Rat
open MeasureTheory Set Filter Topology
open scoped NNReal
set_option autoImplicit false

/-- A rational point inside two prescribed right-hand neighbourhood bounds. -/
theorem solution (t : ℝ≥0) (δ ρ : ℝ) (ht0 : 0 < t)
    (htδ : dist t 0 < δ) (hρ : 0 < ρ) :
    ∃ r : ℚ, r ∈ Ioi (0 : ℚ) ∧ dist r 0 < δ ∧
      Real.toNNReal (r : ℝ) ∈ Ici t ∧ dist (Real.toNNReal (r : ℝ)) t < ρ := by
  have htR : 0 < (t : ℝ) := by exact_mod_cast ht0
  have htδ' : (t : ℝ) < δ := by
    simpa [NNReal.dist_eq, abs_of_nonneg t.coe_nonneg] using htδ
  obtain ⟨r, hr, hr'⟩ := exists_rat_btwn (show (t : ℝ) < min δ ((t : ℝ) + ρ) by
    exact lt_min htδ' (by linarith))
  have hr0 : 0 < (r : ℝ) := htR.trans hr
  let u := Real.toNNReal (r : ℝ)
  have hu : (u : ℝ) = (r : ℝ) := Real.coe_toNNReal (r : ℝ) hr0.le
  have hut : u ∈ Ici t := by
    change t ≤ u
    exact_mod_cast (show (t : ℝ) ≤ (u : ℝ) by rw [hu]; exact hr.le)
  have huρ : dist u t < ρ := by
    rw [NNReal.dist_eq, hu, abs_of_nonneg (sub_nonneg.mpr hr.le)]
    linarith [lt_of_lt_of_le hr' (min_le_right δ ((t : ℝ) + ρ))]
  have hrδ : dist r 0 < δ := by
    rw [Rat.dist_eq, Rat.cast_zero, sub_zero, abs_of_pos hr0]
    exact hr'.trans_le (min_le_left _ _)
  exact ⟨r, by exact_mod_cast hr0, hrδ, hut, huρ⟩
