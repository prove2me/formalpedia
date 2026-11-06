-- Prove2me | solution 1 for GlynnSTS.NoAttain.proposition_4_26
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T04:12:10.258253+00:00
-- url     : https://prove2.me/submissions/862f2da9-f5cc-4dc5-a0eb-f084789b0f02

import Mathlib
import Definitions.Def_GlynnSTS_NoAttain_Setting
import Theorems.Thm_GlynnSTS_NoAttain_C0_subset_D

open MeasureTheory ProbabilityTheory

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (B : Ω → C(unitInterval, ℝ)) (hB : GlynnSTS.Limit.IsStdBMC P B)
    (σ : ℝ) (hσ : 0 < σ) :
    ¬ ∃ g : C(unitInterval, ℝ) → ℝ, GlynnSTS.Limit.ClassM P B g ∧
      ∃ α : ℝ, 0 < α ∧ ∀ᵐ ω ∂P, g (σ • B ω) = α * σ := by
  rintro ⟨g, ⟨_, hhom, _, _, hD⟩, α, hα, h425⟩
  have hsub := GlynnSTS.NoAttain.C0_subset_D P B hB g hhom σ α hσ hα h425
  obtain ⟨_, W, hW, hBW⟩ := hB
  have h1 : ∀ᵐ ω ∂P, B ω ∈ GlynnSTS.Limit.D g := by
    filter_upwards [hW.eval_zero_ae_eq_zero] with ω hω
    apply hsub
    show B ω 0 = 0
    rw [hBW]
    have e : ∀ h, (⟨((0 : unitInterval) : ℝ), h⟩ : NNReal) = 0 := fun h => rfl
    rw [e]
    exact hω
  have h0 : ∀ᵐ ω ∂P, B ω ∉ GlynnSTS.Limit.D g := measure_eq_zero_iff_ae_notMem.mp hD
  obtain ⟨ω, h1, h0⟩ := (h1.and h0).exists
  exact h0 h1
