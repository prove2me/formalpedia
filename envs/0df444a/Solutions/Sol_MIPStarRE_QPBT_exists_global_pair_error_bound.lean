-- Prove2me | solution 1 for MIPStarRE.QPBT.exists_global_pair_error_bound
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T21:42:28.766254+00:00
-- url     : https://prove2.me/submissions/769aadf1-9fc6-47da-9c41-a0388d073468

-- Generated proof for MIPStarRE.QPBT.exists_global_pair_error_bound.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Families
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Interpolation
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_AvgCongr
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_QPBT_QPBT_Combining_ErrorBounds
import Definitions.Def_QPBT_QPBT_Games_ErrorFunctions
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGameMeasurements
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Definitions.Def_QPBT_QPBT_Test_SoundnessDefs
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_MIPStarRE_QPBT_global_pair_error_bound_explicit

namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/-! # Scalar error bounds for combining polynomial measurements

This module proves the formalization-only scalar estimates used by the combining
argument: nonnegativity of the real fourth root, the quarter-power form of a
square root of two deficit terms, polynomial bounds after conditioning,
composition with the dimension factor retained, and absorption into the global
polynomial-pair error scale. The estimates quantify over error functions and
numerical parameters; they do not construct measurements, and none of them is
specific to Claims 17-1 through 17-3.

## References

The auxiliary blueprint statements are `thm:qld-conditioned-polynomial-bound`,
`thm:qld-combining-polynomial-bound`, and `thm:qld-global-pair-error-bound` in
`blueprint/src/chapter/ch15_qpbt_combining.tex`. They support the calculations
in `lem:qld-xz-lines`, `lem:qld-4-13`, and `lem:qld-4-7` of
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:950-963,1134-1246`
and `:1278-1288,1402`. The corrected error notation and the retained dimension
factor are documented in `docs/paper-gaps/qpbt_combined-lines-error-term.tex`.
-/



open MIPStarRE.QPBT

theorem solution (pointError : ℝ → ℝ)
    (hpoint : _root_.MIPStarRE.QPBT.IsPolyErr pointError) (combinedError : ℝ → ℝ → ℝ)
    (hcombined : _root_.MIPStarRE.QPBT.IsPolyErr₂ combinedError)
    (combineConstant soundnessConstant soundnessPower finalScale : ℝ)
    (hcombineConstant : 0 ≤ combineConstant) (hsoundnessConstant : 1 ≤ soundnessConstant)
    (hsoundnessPower : 0 < soundnessPower) (hsoundnessPowerOne : soundnessPower ≤ 1)
    (hfinalScale : 0 ≤ finalScale) :
    ∃ finalConstant finalPower : ℝ, 1 < finalConstant ∧ 0 < finalPower ∧ finalPower < 1 ∧
      ∀ (params : _root_.MIPStarRE.QPBT.AdmissibleParams) (error : ℝ), 0 ≤ error →
        min 1 (finalScale *
          (_root_.MIPStarRE.QPBT.deltaLd soundnessConstant soundnessPower
              (combineConstant * (params.m : ℝ) *
                combinedError error ((params.m * params.d : ℕ) / (params.q : ℝ)) + error)
              params.q (2 * params.m + 2) params.d 1 +
            Real.sqrt (pointError error) + ((params.m * params.d : ℕ) / (params.q : ℝ)))) ≤
          _root_.MIPStarRE.QPBT.deltaQld finalConstant finalPower error params.m params.d params.q := by
  obtain ⟨pointConstant, pointPower, hpointConstant, hpointPower, hpointBound⟩ := hpoint
  obtain ⟨lineConstant, errorPower, ratioPower, hlineConstant,
    herrorPower, hratioPower, hlineBound⟩ := hcombined
  obtain ⟨hA, hB, hBOne, hbound⟩ := _root_.MIPStarRE.QPBT.global_pair_error_bound_explicit pointError
    pointConstant pointPower hpointConstant hpointPower hpointBound combinedError
    lineConstant errorPower ratioPower hlineConstant herrorPower hratioPower hlineBound
    combineConstant soundnessConstant soundnessPower finalScale hcombineConstant
    hsoundnessConstant hsoundnessPower hsoundnessPowerOne hfinalScale
  exact ⟨_root_.MIPStarRE.QPBT.globalPairBoundConstant pointConstant lineConstant combineConstant
      soundnessConstant soundnessPower ratioPower finalScale,
    _root_.MIPStarRE.QPBT.globalPairBoundPower pointPower errorPower ratioPower soundnessPower,
    hA, hB, hBOne, hbound⟩
