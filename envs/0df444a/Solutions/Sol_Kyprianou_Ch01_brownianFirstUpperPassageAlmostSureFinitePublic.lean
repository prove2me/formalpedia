-- Prove2me | solution 1 for Kyprianou.Ch01.brownianFirstUpperPassageAlmostSureFinitePublic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T07:16:32.430966+00:00
-- url     : https://prove2.me/submissions/d9c73bff-9774-4d74-9888-f8490d4f4782

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Theorems.Thm_Kyprianou_Ch01_brownianFirstPassageStableHalf
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
    (B : ℝ≥0 → Ω → ℝ)
    (hB : IsLinearBrownian P B 1 0)
    (hMeas : ∀ t : ℝ≥0, Measurable (B t))
    (s : ℝ) (hs : 0 < s) :
    ∀ᵐ ω ∂P, firstUpperPassage B s ω ≠ ⊤ := by
  obtain ⟨hInt, hMean⟩ :=
    brownianFirstPassageStableHalf P B hB hMeas s 0 hs (le_refl 0)
  have hOne : (∫ ω, passageLaplace (firstUpperPassage B s) 0 ω ∂P) = 1 := by
    simpa using hMean
  have hComplementInt :
      Integrable (fun ω => 1 - passageLaplace (firstUpperPassage B s) 0 ω) P :=
    (integrable_const (1 : ℝ)).sub hInt
  have hComplementNonneg :
      0 ≤ᵐ[P] (fun ω => 1 - passageLaplace (firstUpperPassage B s) 0 ω) := by
    apply Filter.Eventually.of_forall
    intro ω
    cases h : firstUpperPassage B s ω with
    | top => simp [passageLaplace, h]
    | coe t => simp [passageLaplace, h]
  have hComplementZero :
      (∫ ω, 1 - passageLaplace (firstUpperPassage B s) 0 ω ∂P) = 0 := by
    rw [integral_sub (integrable_const (1 : ℝ)) hInt]
    simp [hOne]
  have hAE :=
    (integral_eq_zero_iff_of_nonneg_ae hComplementNonneg
      hComplementInt).mp hComplementZero
  filter_upwards [hAE] with ω hw
  intro hTop
  have hZero : passageLaplace (firstUpperPassage B s) 0 ω = 0 := by
    simp [passageLaplace, hTop]
  simp [hZero] at hw
