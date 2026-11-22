-- Prove2me | solution 2 for Kyprianou.Ch01.branchingToPoissonPathAEMeasurableFromCadlag
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T19:26:53.748627+00:00
-- url     : https://prove2.me/submissions/d38e6733-1229-4ee0-8af8-dab98d136f5d

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_ForwardLampertiPaths
import Theorems.Thm_Kyprianou_Ch01_branchingCadlagJointMeasurableRealVersion
import Theorems.Thm_Kyprianou_Ch01_branchingInverseOccupationMeasurablePathVersion
import Theorems.Thm_Kyprianou_Ch01_branchingPathAEMeasurableFromClockAndJointVersion
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The source Lamperti path measurability follows from a measurable
inverse-clock version and a jointly measurable all-time population version. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (Y : ℝ≥0 → Ω → ℕ) (P : Measure Ω)
    (hMeas : ∀ t : ℝ≥0, Measurable (Y t))
    (hCadlag : ∀ᵐ ω ∂P,
      IsCadlag (fun t : ℝ≥0 => Y t ω)) :
    AEMeasurable
      (fun ω : Ω => fun t : ℝ≥0 =>
        (branchingToPoisson Y t ω : ℤ)) P := by
  obtain ⟨C, hCMeas, hCEq⟩ :=
    Kyprianou.Ch01.branchingInverseOccupationMeasurablePathVersion
      Y P hMeas hCadlag
  obtain ⟨Z, hJoint, hSame⟩ :=
    Kyprianou.Ch01.branchingCadlagJointMeasurableRealVersion
      P Y hMeas hCadlag
  exact Kyprianou.Ch01.branchingPathAEMeasurableFromClockAndJointVersion
    Y P C hCMeas hCEq Z hJoint hSame
