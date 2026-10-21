-- Prove2me | solution 1 for LargeForkJoin.FluidLimit.lemma_4_10
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T12:59:02.138409+00:00
-- url     : https://prove2.me/submissions/786d114d-baf6-4821-96c8-664a0eac7efe

import Mathlib
import Definitions.Def_LargeForkJoin_FluidLimit_Model

open MeasureTheory ProbabilityTheory Filter Topology

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Xp Yp : ℕ → ℝ → Ω → ℝ) (k l : ℝ → ℝ) (t : ℝ)
    (hX : ∀ ε > 0, Tendsto (fun N : ℕ => P {ω | ∃ s ∈ Set.Icc (0 : ℝ) t,
      ε < |Xp N s ω - k s|}) atTop (𝓝 0))
    (hY : ∀ ε > 0, Tendsto (fun N : ℕ => P {ω | ∃ s ∈ Set.Icc (0 : ℝ) t,
      ε < |Yp N s ω - l s|}) atTop (𝓝 0)) :
    ∀ ε > 0, Tendsto (fun N : ℕ => P {ω | ∃ s ∈ Set.Icc (0 : ℝ) t,
      ε < |max (Xp N s ω) (Yp N s ω) - max (k s) (l s)|}) atTop (𝓝 0) := by
  intro ε hε
  have hsum := (hX ε hε).add (hY ε hε)
  rw [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => bot_le) (fun N => ?_)
  refine le_trans (measure_mono ?_) (measure_union_le _ _)
  rintro ω ⟨s, hs, hlt⟩
  have key : |max (Xp N s ω) (Yp N s ω) - max (k s) (l s)| ≤
      max |Xp N s ω - k s| |Yp N s ω - l s| := abs_max_sub_max_le_max _ _ _ _
  by_cases h1 : ε < |Xp N s ω - k s|
  · exact Or.inl ⟨s, hs, h1⟩
  · refine Or.inr ⟨s, hs, ?_⟩
    push Not at h1
    rcases le_total |Xp N s ω - k s| |Yp N s ω - l s| with h | h
    · rw [max_eq_right h] at key; linarith
    · rw [max_eq_left h] at key; linarith
