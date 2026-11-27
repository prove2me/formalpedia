-- Prove2me | solution 1 for Kyprianou.Ch04.gridPairErrorUnionV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:38:44.153475+00:00
-- url     : https://prove2.me/submissions/5625d132-3fae-4f26-91f0-a5aa1d6ea3bd

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Cofinal probability bounds for the finite-variation and martingale parts
combine without assuming the deviation events themselves are measurable. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (T : NNReal) (A B R : ℕ → ℕ → ℕ → NNReal → Ω → ℝ)
    (hR : ∀ m n l t w, R m n l t w = A m n l t w+B m n l t w)
    (hA : ∀ δ : ℝ, 0 < δ → ∀ η : ℝ, 0 < η → ∀ᶠ m in atTop,
      ∀ n, ∀ᶠ l in atTop, (P {w | ∃ t ≤ T, δ ≤ |A m n l t w|}).toReal ≤ η)
    (hB : ∀ δ : ℝ, 0 < δ → ∀ η : ℝ, 0 < η → ∀ᶠ m in atTop,
      ∀ n, ∀ᶠ l in atTop, (P {w | ∃ t ≤ T, δ ≤ |B m n l t w|}).toReal ≤ η) :
    ∀ δ : ℝ, 0 < δ → ∀ η : ℝ, 0 < η → ∀ᶠ m in atTop,
      ∀ n, ∀ᶠ l in atTop, (P {w | ∃ t ≤ T, δ ≤ |R m n l t w|}).toReal ≤ η := by
  intro δ hδ η hη
  filter_upwards [hA (δ/2) (by positivity) (η/2) (by positivity),
    hB (δ/2) (by positivity) (η/2) (by positivity)] with m hmA hmB
  intro n
  filter_upwards [hmA n,hmB n] with l hlA hlB
  let U : Set Ω := {w | ∃ t ≤ T, δ/2 ≤ |A m n l t w|}
  let V : Set Ω := {w | ∃ t ≤ T, δ/2 ≤ |B m n l t w|}
  let W : Set Ω := {w | ∃ t ≤ T, δ ≤ |R m n l t w|}
  have hs : W ⊆ U ∪ V := by
    rintro w ⟨t,ht,hw⟩
    rw [hR] at hw
    by_cases h : δ/2 ≤ |A m n l t w|
    · exact Or.inl ⟨t,ht,h⟩
    · refine Or.inr ⟨t,ht,?_⟩
      have htri := abs_add_le (A m n l t w) (B m n l t w)
      linarith [lt_of_not_ge h]
  have h : P W ≤ P U + P V := (measure_mono hs).trans (measure_union_le U V)
  have h' : (P W).toReal ≤ (P U).toReal + (P V).toReal := by
    rw [← ENNReal.toReal_add (measure_ne_top P U) (measure_ne_top P V)]
    exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨measure_ne_top P U,measure_ne_top P V⟩) h
  change (P U).toReal ≤ η/2 at hlA
  change (P V).toReal ≤ η/2 at hlB
  exact h'.trans (by linarith)
