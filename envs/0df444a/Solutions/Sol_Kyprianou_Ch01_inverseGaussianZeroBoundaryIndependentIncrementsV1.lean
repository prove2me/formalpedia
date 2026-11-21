-- Prove2me | solution 1 for Kyprianou.Ch01.inverseGaussianZeroBoundaryIndependentIncrementsV1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T00:57:18.93245+00:00
-- url     : https://prove2.me/submissions/453dcc2f-d8d1-4110-9141-f118106ab8c4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch01_zeroBoundaryPassageClockMeasurableV1
import Theorems.Thm_Kyprianou_Ch01_independentIncrementsOfJointProductLawV2
import Theorems.Thm_Kyprianou_Ch01_inverseGaussianFirstPassageJointIncrementProductLawV2
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
    ProbabilityTheory.HasIndependentIncrements T P  := by
  let T : ℝ≥0 → Ω → ℝ :=
    fun s ω =>
      if s = 0 then (0 : ℝ)
      else (match Kyprianou.Ch01.firstUpperPassage X (s : ℝ) ω with
      | none => (0 : ℝ)
      | some t => (t : ℝ))
  change HasIndependentIncrements T P
  have hMeasT : ∀ s : ℝ≥0, AEMeasurable (T s) P := by
    intro s
    exact (Kyprianou.Ch01.zeroBoundaryPassageClockMeasurableV1
      X hMeas hContinuous s).aemeasurable
  have hJoint :
      ∀ (n : ℕ) (t : Fin (n + 1) → ℝ≥0),
        Monotone t →
        P.map (fun (ω : Ω) (k : Fin n) =>
          increment T (t k.castSucc) (t k.succ) ω) =
        Measure.pi (fun k : Fin n =>
          P.map (increment T (t k.castSucc) (t k.succ))) :=
    inverseGaussianFirstPassageJointIncrementProductLawV2
      P X b hb hB hMeas hContinuous
  exact independentIncrementsOfJointProductLawV2 P T hMeasT hJoint
