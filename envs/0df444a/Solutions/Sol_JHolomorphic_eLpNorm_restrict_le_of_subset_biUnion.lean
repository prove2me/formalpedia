-- Prove2me | solution 1 for JHolomorphic.eLpNorm_restrict_le_of_subset_biUnion
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-21T23:54:30.928339+00:00
-- url     : https://prove2.me/submissions/371f9c0d-df40-44dc-b5be-6a51e45d8929

import Definitions.Def_JHolomorphic_Setting
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex



namespace JHolomorphic

open MeasureTheory Metric Set
open scoped ENNReal NNReal

theorem eLpNorm_restrict_le_of_subset_biUnion_aux {F : Type*} [NormedAddCommGroup F]
    {f : ℂ → F} (hf : AEStronglyMeasurable f volume) {q : ℝ≥0∞} (hq : 1 ≤ q) (K : Set ℂ) (hKm : MeasurableSet K)
    (t : Finset ℂ) (r : ℝ) (hK : K ⊆ ⋃ x ∈ t, ball x r) (C : ℝ≥0∞)
    (h : ∀ x ∈ t, eLpNorm f q (volume.restrict (ball x r)) ≤ C) :
    eLpNorm f q (volume.restrict K) ≤ t.card * C := by
  set g : ℂ → ℂ → ℝ := fun x z => ‖(ball x r).indicator f z‖ with hg
  have hgm : ∀ x, AEStronglyMeasurable (g x) volume := fun x =>
    (hf.indicator measurableSet_ball).norm
  calc eLpNorm f q (volume.restrict K)
      = eLpNorm (K.indicator f) q volume := by
        rw [eLpNorm_indicator_eq_eLpNorm_restrict hKm]
    _ ≤ eLpNorm (∑ x ∈ t, g x) q volume := by
        refine eLpNorm_mono fun z => ?_
        rw [Finset.sum_apply, Real.norm_eq_abs,
          abs_of_nonneg (Finset.sum_nonneg fun x _ => norm_nonneg _)]
        by_cases hz : z ∈ K
        · obtain ⟨x, hx, hzx⟩ : ∃ x ∈ t, z ∈ ball x r := by simpa using hK hz
          rw [indicator_of_mem hz]
          calc ‖f z‖ = g x z := by rw [hg]; dsimp only; rw [indicator_of_mem hzx]
            _ ≤ ∑ y ∈ t, g y z := Finset.single_le_sum (f := fun y => g y z)
                (fun y _ => norm_nonneg _) hx
        · rw [indicator_of_notMem hz, norm_zero]
          exact Finset.sum_nonneg fun x _ => norm_nonneg _
    _ ≤ ∑ x ∈ t, eLpNorm (g x) q volume := eLpNorm_sum_le (fun x _ => hgm x) hq
    _ = ∑ x ∈ t, eLpNorm f q (volume.restrict (ball x r)) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [hg]; dsimp only
        rw [eLpNorm_norm, eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_ball]
    _ ≤ ∑ _x ∈ t, C := Finset.sum_le_sum h
    _ = t.card * C := by rw [Finset.sum_const, nsmul_eq_mul]

end JHolomorphic

open JHolomorphic

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal NNReal

theorem solution {F : Type*} [NormedAddCommGroup F]
    {f : ℂ → F} (hf : AEStronglyMeasurable f volume) {q : ℝ≥0∞} (hq : 1 ≤ q) (K : Set ℂ)
    (hKm : MeasurableSet K) (t : Finset ℂ) (r : ℝ) (hK : K ⊆ ⋃ x ∈ t, ball x r) (C : ℝ≥0∞)
    (h : ∀ x ∈ t, eLpNorm f q (volume.restrict (ball x r)) ≤ C) :
    eLpNorm f q (volume.restrict K) ≤ t.card * C :=
  eLpNorm_restrict_le_of_subset_biUnion_aux hf hq K hKm t r hK C h
