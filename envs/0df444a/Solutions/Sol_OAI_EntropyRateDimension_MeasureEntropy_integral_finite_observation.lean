-- Prove2me | solution 1 for OAI.EntropyRateDimension.MeasureEntropy.integral_finite_observation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T05:19:40.119818+00:00
-- url     : https://prove2.me/submissions/23656fb9-e08a-46d9-86e3-3da60a4adfbd

import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteDistribution
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_MeasureEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RandomGrid

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.MeasureEntropy
universe uα uβ uγ
open scoped BigOperators ENNReal
open MeasureTheory


theorem solution {α : Type uα} {β : Type uβ} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass β] (μ : Measure α) [IsFiniteMeasure μ]
    (f : α → β) (hf : Measurable f) (s : Finset β) (hs : ∀ᵐ x ∂μ, f x ∈ s)
    (F : β → ℝ) : ∫ x, F (f x) ∂μ = ∑ b ∈ s, mass μ f b*F b := by
  classical
  have hm : ∀ b, MeasurableSet {x | f x = b} := fun b => hf (measurableSet_singleton b)
  have h : ∀ᵐ x ∂μ, F (f x) = ∑ b ∈ s, ({x | f x = b}.indicator (fun _ => F b) x) := by
    filter_upwards [hs] with x hx
    rw [Finset.sum_eq_single (f x)]
    · simp
    · intro b _ hb
      simp [Set.indicator, Ne.symm hb]
    · intro h; exact absurd hx h
  rw [integral_congr_ae h, integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro b _
    rw [integral_indicator_const _ (hm b), smul_eq_mul]
    rfl
  · intro b _
    exact (integrable_const _).indicator (hm b)

