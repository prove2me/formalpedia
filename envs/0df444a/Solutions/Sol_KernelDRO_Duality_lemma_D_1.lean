-- Prove2me | solution 1 for KernelDRO.Duality.lemma_D_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T10:41:25.206515+00:00
-- url     : https://prove2.me/submissions/4ffe48da-b023-4594-8a34-29eb29752d5f

import Mathlib
import Definitions.Def_WassersteinDRO_Duality_erealExpectation
import Definitions.Def_KernelDRO_Duality_Setting
set_option autoImplicit false
open MeasureTheory WassersteinDRO.Duality KernelDRO.Duality

lemma kdd_aux1 (a : EReal) (ha : a ≠ ⊤) (g : ℝ)
    (h : (if (a - (g : EReal)).toENNReal = ⊤ then (⊤ : EReal) else
      (((a - (g : EReal)).toENNReal : ENNReal) : EReal) -
        (((-(a - (g : EReal))).toENNReal : ENNReal) : EReal)) ≤ 0) : a ≤ (g : EReal) := by
  induction a using EReal.rec with
  | bot => exact bot_le
  | coe r =>
    rw [← EReal.coe_sub] at h
    rw [EReal.coe_le_coe_iff]
    by_contra hc
    push Not at hc
    have h1 : (0 : ℝ) < r - g := by linarith
    rw [← EReal.coe_neg] at h
    simp only [EReal.real_coe_toENNReal, ENNReal.ofReal_ne_top, if_false] at h
    rw [ENNReal.ofReal_of_nonpos (by linarith : -(r - g) ≤ 0)] at h
    rw [EReal.coe_ennreal_ofReal, max_eq_left h1.le] at h
    simp only [ENNReal.coe_zero, EReal.coe_ennreal_zero] at h
    have h2 : ((r - g : ℝ) : EReal) ≤ ((0 : ℝ) : EReal) := by simpa using h
    have := EReal.coe_le_coe_iff.1 h2
    linarith
  | top => exact absurd rfl ha

lemma kdd_aux2 (a : EReal) (ha : a ≠ ⊤) (g : ℝ) (h : a ≤ (g : EReal)) :
    (a - (g : EReal)).toENNReal = 0 := by
  rw [EReal.toENNReal_eq_zero_iff]
  induction a using EReal.rec with
  | bot => simp
  | coe r =>
    rw [← EReal.coe_sub]
    rw [EReal.coe_le_coe_iff] at h
    exact_mod_cast sub_nonpos.2 h
  | top => exact absurd rfl ha

theorem solution {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X]
    [BorelSpace X] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (φ : X → H) (hφ : Continuous φ) (l : X → EReal) (hl_usc : UpperSemicontinuous l)
    (hl_top : ∀ ξ, l ξ ≠ ⊤) (f₀ : ℝ) (f : H) :
    (∀ P : ProbabilityMeasure X,
        erealExpectation (P : Measure X)
          (fun ξ => l ξ - ((f₀ + rkhsEval φ f ξ : ℝ) : EReal)) ≤ 0) ↔
      IsDualFeasible φ l f₀ f := by
  constructor
  · intro h ξ
    have h1 := h ⟨Measure.dirac ξ, inferInstance⟩
    unfold erealExpectation at h1
    simp only [ProbabilityMeasure.coe_mk, lintegral_dirac] at h1
    set d : EReal := l ξ - ((f₀ + rkhsEval φ f ξ : ℝ) : EReal) with hd
    exact kdd_aux1 (l ξ) (hl_top ξ) _ h1
  · intro hfeas P
    unfold erealExpectation
    have h0 : ∀ ξ, (l ξ - ((f₀ + rkhsEval φ f ξ : ℝ) : EReal)).toENNReal = 0 := by
      intro ξ
      exact kdd_aux2 (l ξ) (hl_top ξ) _ (hfeas ξ)
    simp only [h0, lintegral_zero]
    simp
    exact EReal.coe_ennreal_nonneg _
