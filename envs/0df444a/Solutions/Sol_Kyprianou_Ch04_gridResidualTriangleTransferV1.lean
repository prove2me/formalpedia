-- Prove2me | solution 1 for Kyprianou.Ch04.gridResidualTriangleTransferV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:02:34.926119+00:00
-- url     : https://prove2.me/submissions/e718d57f-7b72-481d-80e4-77a207ce581e

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

/-- Choose one common cutoff for the two cofinal error estimates. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (T : NNReal) (A : ℕ → ℕ → NNReal → Ω → ℝ) (B : ℕ → NNReal → Ω → ℝ)
    (R : ℕ → ℕ → NNReal → Ω → ℝ)
    (hR : ∀ m n t w, R m n t w = A m n t w + B m t w)
    (hA : ∀ δ : ℝ, 0 < δ → ∀ η : ℝ, 0 < η → ∀ᶠ m in atTop,
      ∀ᶠ n in atTop, (P {w | ∃ t ≤ T, δ ≤ |A m n t w|}).toReal ≤ η)
    (hB : ∀ δ : ℝ, 0 < δ → ∀ η : ℝ, 0 < η → ∀ᶠ m in atTop,
      (P {w | ∃ t ≤ T, δ ≤ |B m t w|}).toReal ≤ η) :
    ∀ δ : ℝ, 0 < δ → ∀ η : ℝ, 0 < η → ∃ m : ℕ,
      ∀ᶠ n in atTop, (P {w | ∃ t ≤ T, δ ≤ |R m n t w|}).toReal ≤ η := by
  intro δ hδ η hη
  obtain ⟨m,hm⟩ := eventually_atTop.mp
    ((hA (δ/2) (by positivity) (η/2) (by positivity)).and
      (hB (δ/2) (by positivity) (η/2) (by positivity)))
  obtain ⟨ha,hb⟩ := hm m le_rfl
  refine ⟨m,?_⟩
  filter_upwards [ha] with n hn
  let U : Set Ω := {w | ∃ t ≤ T, δ/2 ≤ |A m n t w|}
  let V : Set Ω := {w | ∃ t ≤ T, δ/2 ≤ |B m t w|}
  let W : Set Ω := {w | ∃ t ≤ T, δ ≤ |R m n t w|}
  have hsub : W ⊆ U ∪ V := by
    rintro w ⟨t,ht,hw⟩
    rw [hR] at hw
    by_cases h : δ/2 ≤ |A m n t w|
    · exact Or.inl ⟨t,ht,h⟩
    · exact Or.inr ⟨t,ht,by linarith [abs_add_le (A m n t w) (B m t w),lt_of_not_ge h]⟩
  have hUV : (P W).toReal ≤ (P U).toReal + (P V).toReal := by
    rw [← ENNReal.toReal_add (measure_ne_top P U) (measure_ne_top P V)]
    exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨measure_ne_top P U,measure_ne_top P V⟩)
      ((measure_mono hsub).trans (measure_union_le U V))
  change (P W).toReal ≤ η
  change (P U).toReal ≤ η/2 at hn
  change (P V).toReal ≤ η/2 at hb
  linarith
