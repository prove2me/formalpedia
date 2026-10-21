-- Prove2me | solution 1 for ModernOnlineLearning.Reductions.lemma_12_2_convex
-- status  : ACCEPTED   (prove)
-- author  : @suzukasan
-- created : 2026-10-20T17:32:29.604836+00:00
-- url     : https://prove2.me/submissions/a7bb9da4-6c96-4da0-a47d-1466097a3c77

import Definitions.Def_ModernOnlineLearning_Reductions_Setting

set_option autoImplicit false
open ModernOnlineLearning.Reductions

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (V : Set E) (hV : V.Nonempty)
    (hclosed : IsClosed V) (hconv : Convex ℝ V) :
    ConvexOn ℝ Set.univ (distance V) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  rcases hclosed.exists_infDist_eq_dist hV x with ⟨p, hp, hpx⟩
  rcases hclosed.exists_infDist_eq_dist hV y with ⟨q, hq, hqy⟩
  change Metric.infDist (a • x + b • y) V ≤ a * Metric.infDist x V + b * Metric.infDist y V
  calc
    _ ≤ dist (a • x + b • y) (a • p + b • q) :=
      Metric.infDist_le_dist_of_mem (hconv hp hq ha hb hab)
    _ = ‖a • (x-p) + b • (y-q)‖ := by rw [dist_eq_norm]; congr 1; module
    _ ≤ ‖a • (x-p)‖ + ‖b • (y-q)‖ := norm_add_le _ _
    _ = _ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg ha, abs_of_nonneg hb, hpx, hqy, dist_eq_norm, dist_eq_norm]

