-- Prove2me | solution 1 for Kyprianou.Ch04.gridUniformWeightedEnvelopeProbabilityV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:36:37.981904+00:00
-- url     : https://prove2.me/submissions/e03e722a-70c1-488b-b8aa-b244fc6a52d3

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_weightedCompactEnvelopeProbabilityV1
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- A measurable vanishing error envelope times finite samplewise variation
controls every mesh simultaneously in outer probability. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (R : ℕ → ℕ → NNReal → Ω → ℝ) (T : NNReal)
    (C : Ω → ℝ) (D : ℕ → Ω → ℝ≥0∞)
    (hC : Measurable C) (hD : ∀ m, Measurable (D m))
    (hb : ∀ᵐ w ∂P, 0 ≤ C w ∧ ∀ m, D m w ≠ ⊤ →
      ∀ n t, t ≤ T → |R m n t w| ≤ C w * (D m w).toReal)
    (hc : ∀ᵐ w ∂P, ∀ d : ℝ, 0 < d → ∃ N : ℕ, ∀ m ≥ N,
      D m w ≤ ENNReal.ofReal d) :
    ∀ δ : ℝ, 0 < δ → ∀ η : ℝ, 0 < η → ∀ᶠ m in atTop,
      ∀ n, (P {w | ∃ t ≤ T, δ ≤ |R m n t w|}).toReal ≤ η := by
  intro δ hδ η hη
  let Z (m : ℕ) (_ : NNReal) (w : Ω) : ℝ :=
    if D m w = ⊤ then δ else C w*(D m w).toReal
  have hZ : ∀ᵐ w ∂P, 0 ≤ C w ∧ ∀ m, D m w ≠ ⊤ → (0 : ℝ≥0∞) ≠ ⊤ →
      ∀ t ≤ T, |Z m t w| ≤ C w*(D m w).toReal + (0 : ℝ≥0∞).toReal := by
    filter_upwards [hb] with w hw
    refine ⟨hw.1,fun m hm _ t ht => ?_⟩
    simp [Z,hm,abs_of_nonneg (mul_nonneg hw.1 ENNReal.toReal_nonneg)]
  have hconv : ∀ᵐ w ∂P, ∀ d : ℝ, 0 < d → ∃ N : ℕ, ∀ m ≥ N,
      D m w ≤ ENNReal.ofReal d ∧ (0 : ℝ≥0∞) ≤ ENNReal.ofReal d := by
    filter_upwards [hc] with w hw
    intro d hd
    obtain ⟨N,hN⟩ := hw d hd
    exact ⟨N,fun m hm => ⟨hN m hm,by simp⟩⟩
  have hl := Kyprianou.Ch04.weightedCompactEnvelopeProbabilityV1 P Z T C D
    (fun _ _ => 0) hC hD (fun _ => measurable_const) hZ hconv δ hδ
  filter_upwards [hl.eventually (Iio_mem_nhds hη)] with m hm
  intro n
  have hs : ∀ᵐ w ∂P, (∃ t ≤ T, δ ≤ |R m n t w|) → ∃ t ≤ T, δ ≤ |Z m t w| := by
    filter_upwards [hb] with w hw h
    obtain ⟨t,ht,ht'⟩ := h
    refine ⟨0,by positivity,?_⟩
    by_cases hinf : D m w = ⊤
    · simp [Z,hinf,abs_of_pos hδ]
    · simpa [Z,hinf,abs_of_nonneg (mul_nonneg hw.1 ENNReal.toReal_nonneg)] using
        ht'.trans (hw.2 m hinf n t ht)
  have hp := ENNReal.toReal_mono (measure_ne_top P _)
    (measure_mono_ae hs : P {w | ∃ t ≤ T, δ ≤ |R m n t w|} ≤
      P {w | ∃ t ≤ T, δ ≤ |Z m t w|})
  exact hp.trans hm.le
