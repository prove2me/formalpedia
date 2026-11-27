-- Prove2me | solution 1 for Kyprianou.Ch04.normalisedGridProbabilityTransferV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:31:48.44188+00:00
-- url     : https://prove2.me/submissions/903c83f4-6dc9-42c9-8715-b2b0b2e3e9a5

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_outerProbabilityLiminfBoundV1
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Uniform pairwise grid estimates pass to the fixed-mesh path limit, then the
vanishing initial-cell error is restored by the outer-probability union bound. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (T : NNReal)
    (A : ℕ → NNReal → Ω → ℝ) (B I R : ℕ → ℕ → NNReal → Ω → ℝ)
    (hR : ∀ m n t w, R m n t w = (A n t w - B m n t w) + I m n t w)
    (hp : ∀ δ : ℝ, 0 < δ → ∀ η : ℝ, 0 < η → ∀ᶠ m in atTop,
      ∀ n, ∀ᶠ l in atTop, (P {w | ∃ t ≤ T,
        δ ≤ |B l n t w - B m n t w|}).toReal ≤ η)
    (hl : ∀ᵐ w ∂P, ∀ n, ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ l ≥ N,
      ∀ t ≤ T, |B l n t w - A n t w| < δ)
    (hi : ∀ m, ∀ δ : ℝ, 0 < δ → ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop,
      (P {w | ∃ t ≤ T, δ ≤ |I m n t w|}).toReal ≤ η) :
    ∀ δ : ℝ, 0 < δ → ∀ η : ℝ, 0 < η → ∀ᶠ m in atTop, ∀ᶠ n in atTop,
      (P {w | ∃ t ≤ T, δ ≤ |R m n t w|}).toReal ≤ η := by
  intro δ hδ η hη
  filter_upwards [hp (δ/4) (by positivity) (η/2) (by positivity)] with m hm
  filter_upwards [hi m (δ/2) (by positivity) (η/2) (by positivity)] with n hn
  let U : Set Ω := {w | ∃ t ≤ T, δ/2 ≤ |A n t w - B m n t w|}
  let V : Set Ω := {w | ∃ t ≤ T, δ/2 ≤ |I m n t w|}
  let W : Set Ω := {w | ∃ t ≤ T, δ ≤ |R m n t w|}
  have hu : (P U).toReal ≤ η/2 := by
    apply Kyprianou.Ch04.outerProbabilityLiminfBoundV1 P U
      (fun l => {w | ∃ t ≤ T, δ/4 ≤ |B l n t w - B m n t w|}) (η/2)
      (by positivity) (hm n)
    filter_upwards [hl] with w hw hmem
    obtain ⟨t,ht,ht'⟩ := hmem
    obtain ⟨N,hN⟩ := hw n (δ/4) (by positivity)
    refine ⟨N,fun l hl' => ⟨t,ht,?_⟩⟩
    have hsmall := hN l hl' t ht
    have htri := abs_add_le (A n t w - B l n t w) (B l n t w - B m n t w)
    rw [show (A n t w - B l n t w) + (B l n t w - B m n t w) =
      A n t w - B m n t w by ring,abs_sub_comm (A n t w) (B l n t w)] at htri
    linarith
  have hsub : W ⊆ U ∪ V := by
    rintro w ⟨t,ht,hw⟩
    rw [hR] at hw
    by_cases h : δ/2 ≤ |A n t w - B m n t w|
    · exact Or.inl ⟨t,ht,h⟩
    · refine Or.inr ⟨t,ht,?_⟩
      have htri := abs_add_le (A n t w - B m n t w) (I m n t w)
      linarith [lt_of_not_ge h]
  have hUV : (P W).toReal ≤ (P U).toReal + (P V).toReal := by
    rw [← ENNReal.toReal_add (measure_ne_top P U) (measure_ne_top P V)]
    exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨measure_ne_top P U,measure_ne_top P V⟩)
      ((measure_mono hsub).trans (measure_union_le U V))
  change (P W).toReal ≤ η
  change (P V).toReal ≤ η/2 at hn
  linarith
