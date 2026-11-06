-- Prove2me | solution 1 for GlynnSTS.NoAttain.small_ball_positive
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T04:24:08.687122+00:00
-- url     : https://prove2.me/submissions/1727e8e0-a47b-44ed-9bfa-733e6af4495e

import Mathlib
import Definitions.Def_GlynnSTS_NoAttain_Setting
import Theorems.Thm_GlynnSTS_NoAttain_display_4_27

open MeasureTheory ProbabilityTheory

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (B : Ω → C(unitInterval, ℝ)) (hB : GlynnSTS.Limit.IsStdBMC P B) :
    ∀ t : unitInterval, ∀ η z : ℝ, |z| < η →
      0 < P {ω | |B ω t - z| < η ∧ ∀ s : unitInterval, s ≤ t → |B ω s| < 2 * η} := by
  intro t η z hz
  have hη : 0 < η := lt_of_le_of_lt (abs_nonneg z) hz
  rcases eq_or_ne t 0 with rfl | ht
  · obtain ⟨_, W, hW, hBW⟩ := hB
    have h0 : ∀ᵐ ω ∂P, B ω 0 = 0 := by
      filter_upwards [hW.eval_zero_ae_eq_zero] with ω hω
      rw [hBW]
      have e : ∀ h, (⟨((0 : unitInterval) : ℝ), h⟩ : NNReal) = 0 := fun h => rfl
      rw [e]; exact hω
    have hsub : {ω | B ω 0 = 0} ⊆
        {ω | |B ω 0 - z| < η ∧ ∀ s : unitInterval, s ≤ 0 → |B ω s| < 2 * η} := by
      intro ω hω
      simp only [Set.mem_setOf_eq] at hω ⊢
      refine ⟨by rw [hω, zero_sub, abs_neg]; exact hz, fun s hs => ?_⟩
      have : s = 0 := le_antisymm hs (unitInterval.nonneg' )
      rw [this, hω, abs_zero]; linarith
    have hae : ∀ᵐ ω ∂P,
        ω ∈ {ω | |B ω 0 - z| < η ∧ ∀ s : unitInterval, s ≤ 0 → |B ω s| < 2 * η} := by
      filter_upwards [h0] with ω hω using hsub hω
    apply pos_iff_ne_zero.2
    intro hzero
    have hn := measure_eq_zero_iff_ae_notMem.mp hzero
    obtain ⟨ω, h1, h2⟩ := (hae.and hn).exists
    exact h2 h1
  · have htpos : (0:ℝ) < t := lt_of_le_of_ne t.2.1 (fun h => ht (Subtype.ext h.symm))
    let x : C(unitInterval, ℝ) := ⟨fun s => z * min ((s:ℝ) / t) 1, by fun_prop⟩
    have hx0 : x ∈ GlynnSTS.NoAttain.C0 := by
      show z * min (((0:unitInterval):ℝ) / t) 1 = 0
      simp
    have hxt : x t = z := by
      show z * min ((t:ℝ) / t) 1 = z
      rw [div_self htpos.ne', min_self, mul_one]
    have hxb : ∀ s, |x s| ≤ |z| := by
      intro s
      show |z * min ((s:ℝ) / t) 1| ≤ |z|
      rw [abs_mul]
      have h0 : 0 ≤ min ((s:ℝ) / t) 1 := le_min (div_nonneg s.2.1 htpos.le) zero_le_one
      rw [abs_of_nonneg h0]
      exact mul_le_of_le_one_right (abs_nonneg _) (min_le_right _ _)
    have hpos := GlynnSTS.NoAttain.display_4_27 P B hB 1 one_pos x hx0 (η - |z|) (by linarith)
    refine lt_of_lt_of_le hpos (measure_mono ?_)
    intro ω hω
    simp only [Set.mem_setOf_eq, one_smul] at hω ⊢
    have hpt : ∀ s, |B ω s - x s| < η - |z| := fun s =>
      lt_of_le_of_lt (by rw [← Real.dist_eq]; exact ContinuousMap.dist_apply_le_dist s) hω
    refine ⟨?_, fun s _ => ?_⟩
    · have := hpt t; rw [hxt] at this; linarith [abs_nonneg z]
    · have h1 := hpt s
      have h2 := hxb s
      have : |B ω s| ≤ |B ω s - x s| + |x s| := by
        have := abs_add_le (B ω s - x s) (x s); simpa using this
      linarith
