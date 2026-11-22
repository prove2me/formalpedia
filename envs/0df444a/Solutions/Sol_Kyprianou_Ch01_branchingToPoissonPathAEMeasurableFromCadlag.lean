-- Prove2me | solution 1 for Kyprianou.Ch01.branchingToPoissonPathAEMeasurableFromCadlag
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T19:14:38.58327+00:00
-- url     : https://prove2.me/submissions/fd594d33-f508-4f50-a085-51f6eef96c99
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ForwardLampertiPaths
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Theorems.Thm_Kyprianou_Ch01_branchingOccupationFixedTimeAEMeasurableFromCadlag
import Theorems.Thm_Kyprianou_Ch01_branchingCadlagJointMeasurableRealVersion
import Theorems.Thm_Kyprianou_Ch01_aemeasurableCadlagNaturalRandomTimeEvaluation
import Theorems.Thm_Kyprianou_Ch01_branchingToPoissonPathAEMeasurableFromOccupationWitnesses
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The branching random-time process reduces to its proved occupation,
joint-measurability and random-time observation witnesses, followed by
the remaining nontrivial inverse-clock argument. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (Y : ℝ≥0 → Ω → ℕ) (P : Measure Ω)
    (hMeas : ∀ t : ℝ≥0, Measurable (Y t))
    (hCadlag : ∀ᵐ ω ∂P,
      IsCadlag (fun t : ℝ≥0 => Y t ω)) :
    AEMeasurable
      (fun ω : Ω => fun t : ℝ≥0 =>
        (branchingToPoisson Y t ω : ℤ)) P := by
  have hOcc : ∀ t : ℝ≥0,
      AEMeasurable (fun ω : Ω => branchingOccupation Y t ω) P :=
    Kyprianou.Ch01.branchingOccupationFixedTimeAEMeasurableFromCadlag
      P Y hMeas hCadlag
  obtain ⟨Z, hJoint, hSame⟩ :=
    Kyprianou.Ch01.branchingCadlagJointMeasurableRealVersion
      P Y hMeas hCadlag
  have hRandom : ∀ (T : Ω → ℝ≥0), Measurable T →
      AEMeasurable (fun ω : Ω => (Y (T ω) ω : ℝ)) P := by
    intro T hT
    exact Kyprianou.Ch01.aemeasurableCadlagNaturalRandomTimeEvaluation
      P Y hMeas hCadlag T hT
  exact Kyprianou.Ch01.branchingToPoissonPathAEMeasurableFromOccupationWitnesses
    Y P hOcc Z hJoint hSame hRandom
