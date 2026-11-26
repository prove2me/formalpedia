-- Prove2me | solution 1 for Kyprianou.Ch04.compactPairDifferenceBoundV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T15:44:22.178905+00:00
-- url     : https://prove2.me/submissions/7df28258-d1c0-4b6b-b274-af41ada9f701

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal
set_option autoImplicit false

/-- Compact absolute bounds give a genuine finite square supremum for a path difference. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (U V : NNReal → Ω → ℝ) (T : NNReal)
    (hu : ∀ᵐ w ∂P, ∃ C : ℝ, ∀ t ≤ T, |U t w| ≤ C)
    (hv : ∀ᵐ w ∂P, ∃ C : ℝ, ∀ t ≤ T, |V t w| ≤ C) :
    ∀ᵐ w ∂P, BddAbove ((fun t : NNReal => |U t w - V t w|^2) '' Iic T) := by
  filter_upwards [hu,hv] with w hw hw'
  obtain ⟨C,hC⟩ := hw
  obtain ⟨D,hD⟩ := hw'
  refine ⟨(C+D)^2,?_⟩
  rintro _ ⟨t,ht,rfl⟩
  have h := (abs_sub _ _).trans (add_le_add (hC t ht) (hD t ht))
  exact pow_le_pow_left₀ (abs_nonneg _) h 2
