-- Prove2me | solution 1 for Kyprianou.Ch02.levyGaussianZeroOfExponentialGridPowerLowerBoundV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:53:21.724481+00:00
-- url     : https://prove2.me/submissions/92b823ac-982b-4c4b-926c-317755278de4

import Theorems.Thm_Kyprianou_Ch02_levyGridLinearGrowthV1
import Theorems.Thm_Kyprianou_Ch02_levyGaussianQuadraticLowerBoundV1
import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    (a : ℝ) (σ : ℝ≥0) (levyMeasure : Measure ℝ)
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hchar : ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (X t)) ξ =
        Complex.exp ((((t : ℝ) : ℂ)) *
          Kyprianou.Ch01.levyTripleExponent
            ⟨-a, σ ^ 2, levyMeasure, hlevyMeasure⟩ ξ)) :
    (∃ c : ℝ, 0 < c ∧
      ∀ n : ℕ,
        c ≤ (∫ ω, Real.exp (-|X (((n : ℝ≥0) + 1)⁻¹) ω|) ∂P) ^ (n + 1)) →
    σ = 0 := by
  intro h
  obtain ⟨K, hK⟩ := Kyprianou.Ch02.levyGridLinearGrowthV1
    a σ levyMeasure hlevyMeasure P X hX hchar h
  by_contra hn
  have hs : 0 < (σ : ℝ) := by
    exact_mod_cast (pos_iff_ne_zero.mpr hn)
  let z : ℝ := 1 + 4 * (|K| + 1) / (σ : ℝ)^2
  have hz : 1 ≤ z := by
    dsimp [z]
    have h : 0 ≤ 4 * (|K| + 1) / (σ : ℝ)^2 := by positivity
    linarith
  have hq := Kyprianou.Ch02.levyGaussianQuadraticLowerBoundV1
    ⟨-a, σ ^ 2, levyMeasure, hlevyMeasure⟩ z
  have hu := hK z
  rw [abs_of_nonneg (by linarith : 0 ≤ z)] at hu
  simp only [NNReal.coe_pow] at hq
  have hb : (σ : ℝ)^2 * z / 2 = (σ : ℝ)^2 / 2 + 2 * (|K| + 1) := by
    dsimp [z]
    field_simp
    <;> ring
  have h1 : (σ : ℝ)^2 * z / 2 > 2 * |K| := by nlinarith [sq_nonneg (σ : ℝ)]
  have h2 := mul_lt_mul_of_pos_right h1 (show 0 < z by linarith)
  have h3 : K * (1 + z) ≤ 2 * |K| * z := by
    calc
      K * (1 + z) ≤ |K| * (1 + z) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
      _ ≤ 2 * |K| * z := by nlinarith [mul_nonneg (abs_nonneg K) (sub_nonneg.mpr hz)]
  nlinarith
