-- Prove2me | solution 1 for JHolomorphic.eLpNorm_restrict_ne_top_of_forall_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-22T00:26:11.153509+00:00
-- url     : https://prove2.me/submissions/70ed310f-6b41-4204-83e2-5031492a3885

import Definitions.Def_JHolomorphic_Setting



namespace JHolomorphic

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal NNReal

theorem eLpNorm_restrict_ne_top_of_forall_norm_le_aux {F : Type*} [NormedAddCommGroup F]
    {f : ℂ → F} {K : Set ℂ} (hK : IsCompact K) (q : ℝ≥0∞) {B : ℝ}
    (hB : ∀ x ∈ K, ‖f x‖ ≤ B) : eLpNorm f q (volume.restrict K) ≠ ⊤ := by
  refine ne_of_lt (lt_of_le_of_lt (eLpNorm_le_of_ae_bound (C := B) ?_) ?_)
  · exact (ae_restrict_iff' hK.measurableSet).2 (Eventually.of_forall hB)
  · rw [Measure.restrict_apply_univ]
    exact ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by positivity)
      hK.measure_lt_top.ne) ENNReal.ofReal_lt_top

end JHolomorphic

open JHolomorphic

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal NNReal

theorem solution {F : Type*} [NormedAddCommGroup F]
    {f : ℂ → F} {K : Set ℂ} (hK : IsCompact K) (q : ℝ≥0∞) {B : ℝ}
    (hB : ∀ x ∈ K, ‖f x‖ ≤ B) : eLpNorm f q (volume.restrict K) ≠ ⊤ :=
  eLpNorm_restrict_ne_top_of_forall_norm_le_aux hK q hB
