-- Prove2me | solution 1 for Kyprianou.Ch01.brownianPassageHalfStableLevyProcessZeroBoundaryV2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T07:22:03.487158+00:00
-- url     : https://prove2.me/submissions/242fa31d-d21f-4743-a6d9-8b08572848d8

import Theorems.Thm_Kyprianou_Ch01_brownianFirstPassageZeroBoundaryIsLevyProcessPublic
import Theorems.Thm_Kyprianou_Ch01_brownianFirstUpperPassageAlmostSureFinitePublic
import Theorems.Thm_Kyprianou_Ch01_brownianFirstPassageStableHalf
import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Definitions.Def_LeanLevy_Processes_LevyProcess
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal BigOperators
open scoped Classical
set_option autoImplicit false


theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ)
    (hB : Kyprianou.Ch01.IsLinearBrownian P B 1 0)
    (hMeas : ∀ t : ℝ≥0, Measurable (B t))
    (hContinuous : ∀ ω, Continuous (fun t : ℝ≥0 => B t ω)) :
    let T : ℝ≥0 → Ω → ℝ :=
      fun s ω =>
        if s = 0 then (0 : ℝ)
        else (match Kyprianou.Ch01.firstUpperPassage B (s : ℝ) ω with
        | none => (0 : ℝ)
        | some t => (t : ℝ))
    (∀ s : ℝ≥0, 0 < s →
      ∀ᵐ ω ∂P,
        Kyprianou.Ch01.firstUpperPassage B (s : ℝ) ω ≠ ⊤) ∧
    ProbabilityTheory.IsLevyProcess T P ∧
    (∀ (s : ℝ≥0) (q : ℝ), 0 < s → 0 ≤ q →
      Integrable (fun ω => Real.exp (-q * T s ω)) P ∧
      (∫ ω, Real.exp (-q * T s ω) ∂P) =
        Real.exp (-(s : ℝ) * Real.sqrt (2 * q))) := by
  intro T
  refine ⟨?_, ?_, ?_⟩
  · intro s hs
    have hsR : 0 < (s : ℝ) := by exact_mod_cast hs
    exact brownianFirstUpperPassageAlmostSureFinitePublic
      P B hB hMeas (s : ℝ) hsR
  · exact brownianFirstPassageZeroBoundaryIsLevyProcessPublic
      P B hB hMeas hContinuous
  · intro s q hs hq
    have hsR : 0 < (s : ℝ) := by exact_mod_cast hs
    obtain ⟨hInt, hTransform⟩ :=
      brownianFirstPassageStableHalf
        P B hB hMeas (s : ℝ) q hsR hq
    have hFin :=
      brownianFirstUpperPassageAlmostSureFinitePublic
        P B hB hMeas (s : ℝ) hsR
    have hAE :
        (fun ω => Real.exp (-q * T s ω)) =ᵐ[P]
          passageLaplace (firstUpperPassage B (s : ℝ)) q := by
      filter_upwards [hFin] with ω hw
      cases ht : firstUpperPassage B (s : ℝ) ω with
      | top => exact (hw ht).elim
      | coe t =>
          have hsne : s ≠ 0 := ne_of_gt hs
          simp [T, hsne, passageLaplace, ht]
    refine ⟨?_, ?_⟩
    · exact hInt.congr hAE.symm
    · rw [integral_congr_ae hAE]
      exact hTransform
