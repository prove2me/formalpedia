-- Prove2me | solution 1 for NestedSeatAlloc.IntPolicy.theorem1_min_increment_expectation_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T20:23:29.947824+00:00
-- url     : https://prove2.me/submissions/88c1b328-472e-46d8-906e-97fc409f21aa

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

/-!
Proof source for the source-faithful probability step in the level-one
fare-sign argument of `theorem1_subdiff_condition_optimal`: the normalized
increment of `min` is pointwise in `[0,1]`, so its expectation under a
probability measure is also in `[0,1]`.
-/

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : Measurable X)
    {a h : ℝ} (hh : 0 < h) :
    0 ≤ ∫ ω, (min (a + h) (X ω) - min a (X ω)) / h ∂P ∧
      (∫ ω, (min (a + h) (X ω) - min a (X ω)) / h ∂P) ≤ 1 := by
  let q : Ω → ℝ := fun ω =>
    (min (a + h) (X ω) - min a (X ω)) / h
  have hmono : ∀ ω, min a (X ω) ≤ min (a + h) (X ω) := by
    intro ω
    exact min_le_min_right (X ω) (le_add_of_nonneg_right hh.le)
  have hgap : ∀ ω, min (a + h) (X ω) - min a (X ω) ≤ h := by
    intro ω
    by_cases hxa : X ω ≤ a
    · have hxh : X ω ≤ a + h := le_trans hxa (le_add_of_nonneg_right hh.le)
      rw [min_eq_right hxh, min_eq_right hxa]
      linarith
    · by_cases hxh : X ω ≤ a + h
      · have hax : a ≤ X ω := le_of_lt (lt_of_not_ge hxa)
        rw [min_eq_right hxh, min_eq_left hax]
        linarith
      · have hax : a < X ω := lt_of_not_ge hxa
        have hhx : a + h < X ω := lt_of_not_ge hxh
        rw [min_eq_left (le_of_lt hhx), min_eq_left (le_of_lt hax)]
        linarith
  have hqmeas : Measurable q := by
    dsimp [q]
    exact ((measurable_const.min hX).sub (measurable_const.min hX)).div_const h
  have hqbounds : ∀ ω, 0 ≤ q ω ∧ q ω ≤ 1 := by
    intro ω
    constructor
    · exact div_nonneg (sub_nonneg.mpr (hmono ω)) hh.le
    · exact (div_le_one hh).2 (hgap ω)
  have hqint : Integrable q P := by
    apply Integrable.of_bound hqmeas.aestronglyMeasurable 1
    filter_upwards [] with ω
    rcases hqbounds ω with ⟨hq0, hq1⟩
    rw [Real.norm_eq_abs, abs_of_nonneg hq0]
    exact hq1
  have hzero : Integrable (fun _ : Ω => (0 : ℝ)) P := integrable_const 0
  have hone : Integrable (fun _ : Ω => (1 : ℝ)) P := integrable_const 1
  have hlow := integral_mono_ae hzero hqint
    (Filter.Eventually.of_forall fun ω => (hqbounds ω).1)
  have hhigh := integral_mono_ae hqint hone
    (Filter.Eventually.of_forall fun ω => (hqbounds ω).2)
  constructor
  · simpa [q] using hlow
  · simpa [q] using hhigh
