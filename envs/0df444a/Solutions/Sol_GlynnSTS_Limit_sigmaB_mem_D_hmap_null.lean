-- Prove2me | solution 1 for GlynnSTS.Limit.sigmaB_mem_D_hmap_null
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T10:42:38.592204+00:00
-- url     : https://prove2.me/submissions/fea502fa-84e5-4bf5-af89-33b762c56899

import Mathlib
import Definitions.Def_GlynnSTS_Limit_Setting

set_option autoImplicit false
open GlynnSTS.Limit MeasureTheory Filter Topology

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (B : Ω → C(unitInterval, ℝ)) (hB : IsStdBMC P B)
    (g : C(unitInterval, ℝ) → ℝ) (hg : ClassM P B g) (σ : ℝ) (hσ : 0 < σ) :
    P {ω | σ • B ω ∈ D (hmap g)} = 0 := by
  obtain ⟨-, hhom, -, hpos, hnull⟩ := hg
  have hsub : {ω | σ • B ω ∈ D (hmap g)} ⊆ {ω | B ω ∈ D g} ∪ {ω | ¬ 0 < g (B ω)} := by
    intro ω hω
    by_contra hcon
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hcon
    obtain ⟨hcont, hgpos⟩ := hcon
    have hc1 : ContinuousAt g (B ω) := by
      by_contra h
      exact hcont h
    have hgeq : g = fun y => σ * g (σ⁻¹ • y) := by
      funext y
      rw [hhom σ⁻¹ (inv_pos.mpr hσ), mul_inv_cancel_left₀ hσ.ne']
    have hc0 : ContinuousAt g (σ⁻¹ • σ • B ω) := by
      rwa [inv_smul_smul₀ hσ.ne']
    have hc : ContinuousAt (fun y : C(unitInterval, ℝ) => g (σ⁻¹ • y)) (σ • B ω) :=
      hc0.comp (continuous_const_smul σ⁻¹).continuousAt
    have hc2 : ContinuousAt g (σ • B ω) := by
      rw [hgeq]
      exact hc.const_mul σ
    have hne : g (σ • B ω) ≠ 0 := by
      rw [hhom σ hσ]
      exact (mul_pos hσ hgpos).ne'
    have hev : (fun y : C(unitInterval, ℝ) => y 1 / g y) =ᶠ[𝓝 (σ • B ω)] hmap g := by
      filter_upwards [hc2.eventually_ne hne] with y hy
      simp [hmap, hy]
    have hco : ContinuousAt (fun y : C(unitInterval, ℝ) => y 1 / g y) (σ • B ω) :=
      (continuous_eval_const (1 : unitInterval)).continuousAt.div hc2 hne
    exact hω (hco.congr hev)
  exact measure_mono_null hsub (measure_union_null hnull (ae_iff.mp hpos))
