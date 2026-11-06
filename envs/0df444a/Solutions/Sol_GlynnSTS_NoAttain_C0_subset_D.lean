-- Prove2me | solution 1 for GlynnSTS.NoAttain.C0_subset_D
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T04:12:11.191213+00:00
-- url     : https://prove2.me/submissions/04a6c66c-8de7-4896-be7c-030e9afd101c

import Mathlib
import Definitions.Def_GlynnSTS_NoAttain_Setting
import Theorems.Thm_GlynnSTS_NoAttain_display_4_27
import Theorems.Thm_GlynnSTS_NoAttain_not_continuousAt_of_range

open MeasureTheory ProbabilityTheory
open GlynnSTS.NoAttain

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (B : Ω → C(unitInterval, ℝ)) (hB : GlynnSTS.Limit.IsStdBMC P B)
    (g : C(unitInterval, ℝ) → ℝ)
    (hhom : ∀ a : ℝ, 0 < a → ∀ x, g (a • x) = a * g x)
    (σ α : ℝ) (hσ : 0 < σ) (hα : 0 < α)
    (h425 : ∀ᵐ ω ∂P, g (σ • B ω) = α * σ) :
    GlynnSTS.NoAttain.C0 ⊆ GlynnSTS.Limit.D g := by
  intro x hx
  apply GlynnSTS.NoAttain.not_continuousAt_of_range g x α hα
  intro ε hε σ' hσ'
  have hpos := GlynnSTS.NoAttain.display_4_27 P B hB σ' hσ' x hx ε hε
  have hae : ∀ᵐ ω ∂P, g (σ' • B ω) = α * σ' := by
    filter_upwards [h425] with ω hω
    have hc : 0 < σ' / σ := div_pos hσ' hσ
    have : σ' • B ω = (σ' / σ) • (σ • B ω) := by
      rw [smul_smul, div_mul_cancel₀ _ hσ.ne']
    rw [this, hhom _ hc, hω]
    field_simp
  have hne : P {ω | dist (σ' • B ω) x < ε} ≠ 0 := hpos.ne'
  obtain ⟨ω, h1, h2⟩ := (frequently_ae_iff.mpr hne).and_eventually hae |>.exists
  exact ⟨σ' • B ω, h1, h2⟩
