-- Prove2me | solution 1 for MultivarScores.LevelSet.delta_pp_eq
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T11:00:27.89827+00:00
-- url     : https://prove2.me/submissions/a92d4440-b209-4e8f-9bdf-92a3d85fb2f9

import Mathlib
import Definitions.Def_MultivarScores_LevelSet_Setting

set_option autoImplicit false
open MeasureTheory MultivarScores.LevelSet

theorem solution {d : ℕ} (w h : MultivarScores.L2Rule.E d → ℝ)
    (hw_meas : Measurable w) (hw_nonneg : ∀ z, 0 ≤ w z)
    (hh_meas : Measurable h) (hh_nonneg : ∀ z, 0 ≤ h z) (hh_int : Integrable h)
    (α : ℝ) (hα : 0 < α) (A L : Set (MultivarScores.L2Rule.E d)) (hA : MeasurableSet A) (hL : MeasurableSet L)
    (y : MultivarScores.L2Rule.E d) (hwy_int : Integrable (fun z => w (z - y) * h z)) :
    scoreΓ w h α A y - scoreΓ w h α L y =
      ∫ z, (α - w (z - y)) * ((A \ L).indicator 1 z - (L \ A).indicator 1 z) * h z := by
  have hG : Integrable (fun z => (α - w (z - y)) * h z) := by
    refine ((hh_int.const_mul α).sub hwy_int).congr ?_
    filter_upwards with z
    simp only [Pi.sub_apply]; ring
  unfold scoreΓ
  rw [← integral_indicator hA, ← integral_indicator hL, ← integral_sub (hG.indicator hA) (hG.indicator hL)]
  congr 1; funext z
  by_cases hzA : z ∈ A <;> by_cases hzL : z ∈ L <;> simp [Set.indicator, hzA, hzL] <;> ring
