-- Prove2me | solution 1 for Kyprianou.Ch01.inverseGaussianPassageLevySubordinatorZeroBoundaryV2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T07:29:57.500109+00:00
-- url     : https://prove2.me/submissions/49ca702a-4e9d-455d-8547-2c6e2de63883
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Kyprianou_Ch01_inverseGaussianFirstUpperPassageAlmostSureFinitePublic
import Theorems.Thm_Kyprianou_Ch01_inverseGaussianFirstPassageZeroBoundaryIsLevyProcessPublic
import Theorems.Thm_Kyprianou_Ch01_firstUpperPassageLaplaceIntegrableOfContinuousPublic
import Theorems.Thm_Kyprianou_Ch01_inverseGaussianFirstPassageLaplaceRightContinuous
import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Definitions.Def_LeanLevy_Processes_LevyProcess
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
open scoped Classical
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (b : ℝ) (hb : 0 < b)
    (hB : Kyprianou.Ch01.IsLinearBrownian P X 1 b)
    (hMeas : ∀ t : ℝ≥0, Measurable (X t))
    (hContinuous : ∀ ω, Continuous (fun t : ℝ≥0 => X t ω)) :
    let T : ℝ≥0 → Ω → ℝ :=
      fun s ω =>
        if s = 0 then (0 : ℝ)
        else (match Kyprianou.Ch01.firstUpperPassage X (s : ℝ) ω with
        | none => (0 : ℝ)
        | some t => (t : ℝ))
    (∀ s : ℝ≥0, 0 < s →
      ∀ᵐ ω ∂P,
        Kyprianou.Ch01.firstUpperPassage X (s : ℝ) ω ≠ ⊤) ∧
      ProbabilityTheory.IsLevyProcess T P ∧
      (∀ (s : ℝ≥0) (q : ℝ), 0 < s → 0 ≤ q →
        Integrable (fun ω => Real.exp (-q * T s ω)) P ∧
        (∫ ω, Real.exp (-q * T s ω) ∂P) =
          Real.exp (-(s : ℝ) *
            (Real.sqrt (b ^ 2 + 2 * q) - b))) := by
  intro T
  refine ⟨?_, ?_, ?_⟩
  · intro s hs
    have hsR : 0 < (s : ℝ) := by exact_mod_cast hs
    exact inverseGaussianFirstUpperPassageAlmostSureFinitePublic
      P X b (s : ℝ) hb hsR hB hMeas
  · exact inverseGaussianFirstPassageZeroBoundaryIsLevyProcessPublic
      P X b hb hB hMeas hContinuous
  · intro s q hs hq
    have hsR : 0 < (s : ℝ) := by exact_mod_cast hs
    have hFin := inverseGaussianFirstUpperPassageAlmostSureFinitePublic
      P X b (s : ℝ) hb hsR hB hMeas
    have hInt :=
      firstUpperPassageLaplaceIntegrableOfContinuousPublic
        P X hMeas hContinuous (s : ℝ) q hq
    have hAE :
        (fun ω => Real.exp (-q * T s ω)) =ᵐ[P]
          passageLaplace (firstUpperPassage X (s : ℝ)) q := by
      filter_upwards [hFin] with ω hw
      cases ht : firstUpperPassage X (s : ℝ) ω with
      | top => exact (hw ht).elim
      | coe t =>
          have hsne : s ≠ 0 := ne_of_gt hs
          simp [T, hsne, passageLaplace, ht]
    obtain ⟨_, hTransform⟩ :=
      inverseGaussianFirstPassageLaplaceRightContinuous
        P X b (s : ℝ) hb hsR hB hMeas hContinuous
    refine ⟨?_, ?_⟩
    · exact hInt.congr hAE.symm
    · rw [integral_congr_ae hAE]
      simpa only [neg_mul] using hTransform q hq
