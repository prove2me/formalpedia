-- Prove2me | solution 1 for Kyprianou.exercise2_3_AllPartsCh02V3
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-15T21:04:11.079117+00:00
-- url     : https://prove2.me/submissions/692dc3ee-95d0-4aec-be3c-afdf4ca7f8b0

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration

open MeasureTheory ProbabilityTheory Filter Complex
open scoped NNReal ENNReal
set_option autoImplicit false

lemma kyp23_upper (φ x : ℝ) (hφ : 0 < φ) (hx : 0 ≤ x) :
    1 - Real.exp (-φ * x) ≤ max 1 φ * min 1 x := by
  rcases le_total x 1 with h | h
  · rw [min_eq_right h]
    have h1 : 1 - φ * x ≤ Real.exp (-φ * x) := by
      have := Real.add_one_le_exp (-φ * x); linarith
    have h2 : φ * x ≤ max 1 φ * x := mul_le_mul_of_nonneg_right (le_max_right _ _) hx
    linarith
  · rw [min_eq_left h, mul_one]
    have := Real.exp_pos (-φ * x)
    have := le_max_left 1 φ
    linarith

lemma kyp23_lower (x : ℝ) (hx : 0 ≤ x) :
    min 1 x * (1 - Real.exp (-1)) ≤ 1 - Real.exp (-1 * x) := by
  rcases le_total x 1 with h | h
  · rw [min_eq_right h]
    have hc := convexOn_exp.2 (Set.mem_univ (0:ℝ)) (Set.mem_univ (-1:ℝ))
      (show 0 ≤ 1 - x by linarith) hx (by ring)
    simp only [smul_eq_mul, Real.exp_zero] at hc
    have : (1 - x) * 0 + x * -1 = -1 * x := by ring
    rw [this] at hc
    nlinarith
  · rw [min_eq_left h, one_mul]
    have : Real.exp (-1 * x) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
    linarith

theorem part1
    {E : Type} [MeasurableSpace E] (η : Measure E)
    (f : E → ℝ) (hf : Measurable f)
    (hnonneg : ∀ x, 0 ≤ f x) :
      (∫⁻ x, ENNReal.ofReal (min 1 (f x)) ∂η) < ⊤ →
    (∀ (φ : ℝ), 0 < φ →
      (∫⁻ x, ENNReal.ofReal
        (1 - Real.exp (-φ * f x)) ∂η) < ⊤) := by
  intro h φ hφ
  calc (∫⁻ x, ENNReal.ofReal (1 - Real.exp (-φ * f x)) ∂η)
      ≤ ∫⁻ x, ENNReal.ofReal (max 1 φ) * ENNReal.ofReal (min 1 (f x)) ∂η := by
        apply lintegral_mono
        intro x
        dsimp only
        rw [← ENNReal.ofReal_mul (by positivity)]
        exact ENNReal.ofReal_le_ofReal (kyp23_upper φ (f x) hφ (hnonneg x))
    _ = ENNReal.ofReal (max 1 φ) * ∫⁻ x, ENNReal.ofReal (min 1 (f x)) ∂η :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top h

theorem part2
    {E : Type} [MeasurableSpace E] (η : Measure E)
    (f : E → ℝ) (hf : Measurable f)
    (hnonneg : ∀ x, 0 ≤ f x) :
    (∀ (φ : ℝ), 0 < φ →
      (∫⁻ x, ENNReal.ofReal
        (1 - Real.exp (-φ * f x)) ∂η) < ⊤) →
      (∫⁻ x, ENNReal.ofReal (min 1 (f x)) ∂η) < ⊤ := by
  intro h
  have h1 := h 1 one_pos
  have hc : 0 < 1 - Real.exp (-1) := by
    have : Real.exp (-1) < 1 := by rw [Real.exp_lt_one_iff]; norm_num
    linarith
  calc (∫⁻ x, ENNReal.ofReal (min 1 (f x)) ∂η)
      ≤ ∫⁻ x, ENNReal.ofReal (1 / (1 - Real.exp (-1))) *
          ENNReal.ofReal (1 - Real.exp (-1 * f x)) ∂η := by
        apply lintegral_mono
        intro x
        dsimp only
        rw [← ENNReal.ofReal_mul (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hc]
        exact kyp23_lower (f x) (hnonneg x)
    _ = ENNReal.ofReal (1 / (1 - Real.exp (-1))) *
          ∫⁻ x, ENNReal.ofReal (1 - Real.exp (-1 * f x)) ∂η :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top h1

theorem solution
    {E : Type} [MeasurableSpace E] (η : Measure E)
    (f : E → ℝ) (hf : Measurable f)
    (hnonneg : ∀ x, 0 ≤ f x) :
    (∀ (φ : ℝ), 0 < φ →
      (∫⁻ x, ENNReal.ofReal
        (1 - Real.exp (-φ * f x)) ∂η) < ⊤) ↔
      (∫⁻ x, ENNReal.ofReal (min 1 (f x)) ∂η) < ⊤ :=
  ⟨part2 η f hf hnonneg, part1 η f hf hnonneg⟩
