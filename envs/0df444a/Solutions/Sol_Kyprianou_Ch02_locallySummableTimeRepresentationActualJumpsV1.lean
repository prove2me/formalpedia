-- Prove2me | solution 1 for Kyprianou.Ch02.locallySummableTimeRepresentationActualJumpsV1
-- status  : ACCEPTED   (prove)
-- author  : @ytako6706
-- created : 2026-11-24T04:32:20.70157+00:00
-- url     : https://prove2.me/submissions/c6e1e9fe-7500-4ff0-8dac-472cb1c88ce7

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_real_atomic_step_tsum_tendsto_left

open MeasureTheory ProbabilityTheory Function Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (f g : ℝ≥0 → ℝ) (d : ℝ)
    (hs : ∀ T : ℝ≥0, Summable (fun s : Set.Ioc (0 : ℝ≥0) T => |g s|))
    (heq : ∀ T : ℝ≥0, f T = d * (T : ℝ) +
      ∑' s : Set.Ioc (0 : ℝ≥0) T, g s) :
    ∀ t : ℝ≥0, 0 < t → f t - leftLim f t = g t := by
  intro t ht
  -- the marks truncated at the horizon `t`, extended by zero
  set F : ℝ≥0 → ℝ := (Set.Ioc (0 : ℝ≥0) t).indicator g with hF
  have hFabs : Summable (fun u => |F u|) := by
    have hrw : (fun u => |F u|) = (Set.Ioc (0 : ℝ≥0) t).indicator (fun u => |g u|) := by
      funext u
      by_cases hu : u ∈ Set.Ioc (0 : ℝ≥0) t
      · simp [hF, Set.indicator_of_mem hu]
      · simp [hF, Set.indicator_of_notMem hu]
    rw [hrw, ← summable_subtype_iff_indicator]
    exact hs t
  have hFsum : Summable F := hFabs.of_abs
  -- subtype sums are indicator sums
  have hsub : ∀ T : ℝ≥0, (∑' s : Set.Ioc (0 : ℝ≥0) T, g s) =
      ∑' u : ℝ≥0, (Set.Ioc (0 : ℝ≥0) T).indicator g u := fun T => tsum_subtype _ _
  -- the strict-past sum is the limit from the left
  have hleft :=
    AvramDividend.Classical.avram_p3_a_bvdrift_real_atomic_step_tsum_tendsto_left F hFabs t ht
  have htend : Tendsto f (𝓝[<] t)
      (𝓝 (d * (t : ℝ) + ∑' u : ℝ≥0, if 0 < u ∧ u < t then F u else 0)) := by
    have h1 : Tendsto (fun s : ℝ≥0 => d * (s : ℝ)) (𝓝[<] t) (𝓝 (d * (t : ℝ))) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds
      exact ((continuous_const.mul NNReal.continuous_coe).tendsto t)
    refine (h1.add hleft).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs'
    have hst : s < t := hs'
    rw [heq s, hsub s]
    congr 2
    funext u
    by_cases hu : 0 < u ∧ u ≤ s
    · have hu' : u ∈ Set.Ioc (0 : ℝ≥0) t := ⟨hu.1, hu.2.trans hst.le⟩
      have hu'' : u ∈ Set.Ioc (0 : ℝ≥0) s := ⟨hu.1, hu.2⟩
      rw [if_pos hu, hF, Set.indicator_of_mem hu', Set.indicator_of_mem hu'']
    · have hu'' : u ∉ Set.Ioc (0 : ℝ≥0) s := fun h => hu ⟨h.1, h.2⟩
      rw [if_neg hu, Set.indicator_of_notMem hu'']
  have hne : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, ht⟩
  have hll := leftLim_eq_of_tendsto htend
  -- the difference of the inclusive and strict sums is the mark at `t`
  have hsum2 : Summable (fun u : ℝ≥0 => if 0 < u ∧ u < t then F u else 0) := by
    refine Summable.of_norm_bounded hFabs (fun u => ?_)
    split_ifs
    · simp [Real.norm_eq_abs]
    · simp
  have hdiff : (∑' u, F u) - (∑' u : ℝ≥0, if 0 < u ∧ u < t then F u else 0) = g t := by
    rw [← hFsum.tsum_sub hsum2]
    have hpt : (fun u : ℝ≥0 => F u - if 0 < u ∧ u < t then F u else 0) =
        fun u => if u = t then g t else 0 := by
      funext u
      rcases lt_trichotomy u t with hlt | rfl | hgt
      · have hne' : u ≠ t := ne_of_lt hlt
        by_cases h0 : 0 < u
        · rw [if_pos ⟨h0, hlt⟩, if_neg hne', sub_self]
        · have hu : u ∉ Set.Ioc (0 : ℝ≥0) t := fun h => h0 h.1
          rw [if_neg (fun h => h0 h.1), if_neg hne', hF, Set.indicator_of_notMem hu, sub_zero]
      · have hu : u ∈ Set.Ioc (0 : ℝ≥0) u := ⟨ht, le_rfl⟩
        rw [if_neg (fun h => lt_irrefl u h.2), if_pos rfl, hF, Set.indicator_of_mem hu,
          sub_zero]
      · have hne' : u ≠ t := ne_of_gt hgt
        have hu : u ∉ Set.Ioc (0 : ℝ≥0) t := fun h => absurd h.2 (not_le.mpr hgt)
        rw [if_neg (fun h => absurd h.2 (not_lt.mpr hgt.le)), if_neg hne', hF,
          Set.indicator_of_notMem hu, sub_zero]
    rw [hpt, tsum_ite_eq]
  rw [hll, heq t, hsub t]
  have hFt : (fun u => (Set.Ioc (0 : ℝ≥0) t).indicator g u) = F := rfl
  rw [hFt]
  linarith
