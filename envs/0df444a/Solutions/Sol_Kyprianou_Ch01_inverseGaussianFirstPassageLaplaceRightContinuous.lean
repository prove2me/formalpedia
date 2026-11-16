-- Prove2me | solution 1 for Kyprianou.Ch01.inverseGaussianFirstPassageLaplaceRightContinuous
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T19:26:23.035707+00:00
-- url     : https://prove2.me/submissions/e3babf15-c8d1-492b-b3b2-6acee1ca96a2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanRightContinuousFiltration
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch01_inverseGaussianFirstPassageLaplace
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The raw generated filtration grows with physical time. -/
private theorem naturalSigma_mono_for_right
    {Ω : Type*} [MeasurableSpace Ω] (X : ℝ≥0 → Ω → ℝ)
    {t s : ℝ≥0} (hts : t ≤ s) :
    naturalSigma X t ≤ naturalSigma X s := by
  change PerfCorrMSQ.natFiltr X t ≤ PerfCorrMSQ.natFiltr X s
  unfold PerfCorrMSQ.natFiltr
  refine iSup_le fun u => iSup_le fun hu => ?_
  exact le_iSup_of_le u (le_iSup_of_le (le_trans hu hts) le_rfl)

/-- A stopping time in the raw natural filtration is also right-natural. -/
private theorem rawStopping_implies_right
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ) (τ : Ω → WithTop ℝ≥0)
    (hτ : IsNaturalStoppingTime X τ) :
    IsNaturalRightStoppingTime X τ := by
  intro t
  have hle : naturalSigma X t ≤ naturalSigmaRight X t := by
    unfold naturalSigmaRight
    refine le_iInf fun s => le_iInf fun hs => ?_
    exact naturalSigma_mono_for_right X (le_of_lt hs)
  exact hle _ (hτ t)

/-- The inverse-Gaussian transform in the right-continuous filtration
    follows from the source-exact raw-stopping-time transform. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (b s : ℝ)
    (hb : 0 < b) (hs : 0 < s)
    (hB : IsLinearBrownian P X 1 b)
    (hXmeas : ∀ t : ℝ≥0, Measurable (X t))
    (hAllContinuous : ∀ ω, Continuous (fun t : ℝ≥0 => X t ω)) :
    IsNaturalRightStoppingTime X (firstUpperPassage X s) ∧
      ∀ q : ℝ, 0 ≤ q →
        (∫ ω, passageLaplace (firstUpperPassage X s) q ω ∂P) =
          Real.exp (-(s * (Real.sqrt (b ^ 2 + 2 * q) - b))) := by
  obtain ⟨hraw, hlap⟩ :=
    Kyprianou.Ch01.inverseGaussianFirstPassageLaplace
      P X b s hb hs hB hXmeas hAllContinuous
  exact ⟨rawStopping_implies_right X (firstUpperPassage X s) hraw, hlap⟩
