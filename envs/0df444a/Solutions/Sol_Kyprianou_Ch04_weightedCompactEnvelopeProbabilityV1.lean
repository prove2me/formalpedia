-- Prove2me | solution 1 for Kyprianou.Ch04.weightedCompactEnvelopeProbabilityV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:19:35.064594+00:00
-- url     : https://prove2.me/submissions/4e1fc0da-fe1b-4377-b062-3a09e55f3a2c

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_outerAEEventTailV1
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Finite pathwise variation may multiply a vanishing measurable error envelope
without requiring an integrable variation bound. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (R : ℕ → NNReal → Ω → ℝ) (T : NNReal)
    (C : Ω → ℝ) (D E : ℕ → Ω → ℝ≥0∞)
    (hC : Measurable C) (hD : ∀ m, Measurable (D m))
    (hE : ∀ m, Measurable (E m))
    (hb : ∀ᵐ w ∂P, 0 ≤ C w ∧ ∀ m, D m w ≠ ⊤ → E m w ≠ ⊤ →
      ∀ t ≤ T, |R m t w| ≤ C w * (D m w).toReal + (E m w).toReal)
    (hc : ∀ᵐ w ∂P, ∀ d : ℝ, 0 < d → ∃ N : ℕ, ∀ m ≥ N,
      D m w ≤ ENNReal.ofReal d ∧ E m w ≤ ENNReal.ofReal d)
    (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun m => (P {w | ∃ t ≤ T, δ ≤ |R m t w|}).toReal) atTop (nhds 0) := by
  let B (m : ℕ) : Set Ω := {w | D m w = ⊤} ∪ {w | E m w = ⊤} ∪
    {w | δ ≤ C w * (D m w).toReal + (E m w).toReal}
  apply Kyprianou.Ch04.outerAEEventTailV1 P _ B
  · intro m
    exact ((measurableSet_eq_fun (hD m) measurable_const).union
      (measurableSet_eq_fun (hE m) measurable_const)).union
      (measurableSet_le measurable_const
        ((hC.mul (ENNReal.measurable_toReal.comp (hD m))).add
          (ENNReal.measurable_toReal.comp (hE m))))
  · intro m
    filter_upwards [hb] with w hw h
    obtain ⟨t,ht,hd⟩ := h
    by_cases h1 : D m w = ⊤
    · exact Or.inl (Or.inl h1)
    by_cases h2 : E m w = ⊤
    · exact Or.inl (Or.inr h2)
    exact Or.inr (hd.trans (hw.2 m h1 h2 t ht))
  · filter_upwards [hb,hc] with w hw hc'
    let d := δ / (2 * (C w + 1))
    have hd : 0 < d := div_pos hδ (by linarith [hw.1])
    obtain ⟨N,hN⟩ := hc' d hd
    refine ⟨N,fun m hm hmem => ?_⟩
    obtain ⟨h1,h2⟩ := hN m hm
    have h1' : D m w ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top h1
    have h2' : E m w ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top h2
    have h3 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
    have h4 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h2
    rw [ENNReal.toReal_ofReal hd.le] at h3 h4
    rcases hmem with (h | h) | h
    · exact h1' h
    · exact h2' h
    · have hh := mul_le_mul_of_nonneg_left h3 hw.1
      have he : (C w + 1) * d = δ / 2 := by
        dsimp [d]
        have hn : C w + 1 ≠ 0 := by linarith [hw.1]
        field_simp [hn]
      change δ ≤ C w * (D m w).toReal + (E m w).toReal at h
      nlinarith [hh,h3,h4,he,hδ]
