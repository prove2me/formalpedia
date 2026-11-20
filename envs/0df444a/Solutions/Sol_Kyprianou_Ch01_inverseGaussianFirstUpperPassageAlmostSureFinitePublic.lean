-- Prove2me | solution 1 for Kyprianou.Ch01.inverseGaussianFirstUpperPassageAlmostSureFinitePublic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T07:20:22.630274+00:00
-- url     : https://prove2.me/submissions/e82a9151-1016-4d94-be83-96ad8cb54bb5

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Theorems.Thm_Kyprianou_Ch01_inverseGaussianZeroDiscountPositiveDrift
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (b s : ℝ)
    (hb : 0 < b) (hs : 0 < s)
    (hB : IsLinearBrownian P X 1 b)
    (hMeas : ∀ t : ℝ≥0, Measurable (X t)) :
    ∀ᵐ ω ∂P, firstUpperPassage X s ω ≠ ⊤ := by
  obtain ⟨hInt, hMean⟩ :=
    inverseGaussianZeroDiscountPositiveDrift P X b s hb hs hB hMeas
  have hComplementInt :
      Integrable (fun ω => 1 - passageLaplace (firstUpperPassage X s) 0 ω) P :=
    (integrable_const (1 : ℝ)).sub hInt
  have hComplementNonneg :
      0 ≤ᵐ[P] (fun ω => 1 - passageLaplace (firstUpperPassage X s) 0 ω) := by
    apply Filter.Eventually.of_forall
    intro ω
    cases h : firstUpperPassage X s ω with
    | top => simp [passageLaplace, h]
    | coe t => simp [passageLaplace, h]
  have hComplementZero :
      (∫ ω, 1 - passageLaplace (firstUpperPassage X s) 0 ω ∂P) = 0 := by
    rw [integral_sub (integrable_const (1 : ℝ)) hInt]
    simp [hMean]
  have hAE :=
    (integral_eq_zero_iff_of_nonneg_ae hComplementNonneg
      hComplementInt).mp hComplementZero
  filter_upwards [hAE] with ω hw
  intro hTop
  have hZero : passageLaplace (firstUpperPassage X s) 0 ω = 0 := by
    simp [passageLaplace, hTop]
  simp [hZero] at hw
