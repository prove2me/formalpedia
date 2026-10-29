-- Prove2me | solution 1 for MIPStarRE.QPBT.ExtendedLineGame.seven_branch_rejections_le
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T02:45:43.028331+00:00
-- url     : https://prove2.me/submissions/66f772b7-6b39-46bc-9d21-36989f528757

-- Generated proof for MIPStarRE.QPBT.ExtendedLineGame.seven_branch_rejections_le.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
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
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_LowDegreeCode
import Definitions.Def_QPBT_QPBT_Combining_Defs
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Game
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_GameValue
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Definitions.Def_QPBT_QPBT_Combining_ExtendedLineGame
import Definitions.Def_QPBT_QPBT_Combining_ExtendedLineGame_ParameterEvaluatedLineBound
import Definitions.Def_QPBT_QPBT_Combining_ExtendedLineGame_SameLineCoefficientBound
import Definitions.Def_QPBT_QPBT_Combining_Witnesses
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistributionAux
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_MIPStarRE_QPBT_ExtendedLineGame_aline_aline_rejection_le_axisParameterEvaluatedCoefficientDefect_add
import Theorems.Thm_MIPStarRE_QPBT_ExtendedLineGame_aline_point_rejection_eq_completedLinePointDefect
import Theorems.Thm_MIPStarRE_QPBT_ExtendedLineGame_axis_parameter_evaluated_coefficient_defect_eq
import Theorems.Thm_MIPStarRE_QPBT_ExtendedLineGame_axis_parameter_evaluation_defect_le
import Theorems.Thm_MIPStarRE_QPBT_ExtendedLineGame_diagonal_parameter_evaluated_coefficient_defect_eq
import Theorems.Thm_MIPStarRE_QPBT_ExtendedLineGame_diagonal_parameter_evaluation_defect_le
import Theorems.Thm_MIPStarRE_QPBT_ExtendedLineGame_dline_dline_rejection_le_diagonalParameterEvaluatedCoefficientDefect_add
import Theorems.Thm_MIPStarRE_QPBT_ExtendedLineGame_dline_point_rejection_eq_completedLinePointDefect
import Theorems.Thm_MIPStarRE_QPBT_ExtendedLineGame_point_aline_rejection_eq_completedLinePointDefect
import Theorems.Thm_MIPStarRE_QPBT_ExtendedLineGame_point_dline_rejection_eq_completedLinePointDefect
import Theorems.Thm_MIPStarRE_QPBT_ExtendedLineGame_point_point_rejection_le
import Theorems.Thm_MIPStarRE_QPBT_WinImplications_avgOver_mix
import Theorems.Thm_MIPStarRE_QPBT_extendedDirectLd_coefficientCollisionLoss_le_five_mul

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.ExtendedLineGame
end MIPStarRE.QPBT.ExtendedLineGame

/- Source helpers from QPBT/Combining/ExtendedLineGame.lean. -/
/-!
# A direct-game strategy from supplied extended-line measurements

The input is an existing `ExtendedLinesWitness`, not an existence assertion
for that witness. Axis answers are restricted using its degree-support field;
diagonal answers are extended by zero coefficients. Point answers are the
scalar coarse-grainings of the supplied joint point measurements.

These are construction lemmas for the first paragraph of the proof of
`lem:qld-4-7`, not a proof of that lemma or of the existence of its input.
The remaining game-value estimates and the dependency on issue Dengnifer/MIPStarRE-QPBT-bak#119 are
recorded in `audits/2026-09-06_extended-line-game-244.md`.

## References

- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1020-1034`
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1267-1402`
- Blueprint `lem:qld-4-7` and `rem:qld-4-7-divisibility`.
- `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

namespace ExtendedLineGame





























variable {params : _root_.MIPStarRE.QPBT.AdmissibleParams} {epsilon deltaQ deltaL : ℝ}
variable {setting : _root_.MIPStarRE.QPBT.ProjectiveSetting params epsilon}
variable {points : _root_.MIPStarRE.QPBT.CombinedPointsWitness setting deltaQ}













/-- Exact separation of the witness's equal axis/diagonal mixture. -/
theorem completedLinePointDefect_eq_half_sum
    (lines : _root_.MIPStarRE.QPBT.ExtendedLinesWitness setting points deltaL)
    (linePlacement pointPlacement : _root_.MIPStarRE.QPBT.Placement) :
    _root_.MIPStarRE.QPBT.ExtendedLineGame.completedLinePointDefect lines linePlacement pointPlacement
        (_root_.MIPStarRE.QPBT.directLinePointDist params.extendedDirectLd) =
      (_root_.MIPStarRE.QPBT.ExtendedLineGame.completedLinePointDefect lines linePlacement pointPlacement
          (_root_.MIPStarRE.QPBT.directALinePointDist params.extendedDirectLd) +
        _root_.MIPStarRE.QPBT.ExtendedLineGame.completedLinePointDefect lines linePlacement pointPlacement
          (_root_.MIPStarRE.QPBT.directDLinePointDist params.extendedDirectLd)) / 2 := by
  unfold _root_.MIPStarRE.QPBT.ExtendedLineGame.completedLinePointDefect _root_.MIPStarRE.QPBT.consistencyDefect
  rw [_root_.MIPStarRE.QPBT.directLinePointDist, _root_.MIPStarRE.QPBT.WinImplications.avgOver_mix]
  ring

/-- Both oriented sums of axis and diagonal completed defects are bounded by
`2 * deltaL`, using exactly the two consistency fields supplied by `lines`.
Identifying these quantities with game rejection requires the separate
register-correlation transport recorded in the packet audit. -/
theorem completedLinePointDefect_sums_le
    (lines : _root_.MIPStarRE.QPBT.ExtendedLinesWitness setting points deltaL) :
    (_root_.MIPStarRE.QPBT.ExtendedLineGame.completedLinePointDefect lines .AA' .BA''
        (_root_.MIPStarRE.QPBT.directALinePointDist params.extendedDirectLd) +
      _root_.MIPStarRE.QPBT.ExtendedLineGame.completedLinePointDefect lines .AA' .BA''
        (_root_.MIPStarRE.QPBT.directDLinePointDist params.extendedDirectLd) ≤ 2 * deltaL) ∧
    (_root_.MIPStarRE.QPBT.ExtendedLineGame.completedLinePointDefect lines .BB' .AB''
        (_root_.MIPStarRE.QPBT.directALinePointDist params.extendedDirectLd) +
      _root_.MIPStarRE.QPBT.ExtendedLineGame.completedLinePointDefect lines .BB' .AB''
        (_root_.MIPStarRE.QPBT.directDLinePointDist params.extendedDirectLd) ≤ 2 * deltaL) := by
  constructor
  · have hbound : _root_.MIPStarRE.QPBT.ExtendedLineGame.completedLinePointDefect lines .AA' .BA''
        (_root_.MIPStarRE.QPBT.directLinePointDist params.extendedDirectLd) ≤ deltaL := lines.consistent_alice
    rw [_root_.MIPStarRE.QPBT.ExtendedLineGame.completedLinePointDefect_eq_half_sum] at hbound
    linarith
  · have hbound : _root_.MIPStarRE.QPBT.ExtendedLineGame.completedLinePointDefect lines .BB' .AB''
        (_root_.MIPStarRE.QPBT.directLinePointDist params.extendedDirectLd) ≤ deltaL := lines.consistent_bob
    rw [_root_.MIPStarRE.QPBT.ExtendedLineGame.completedLinePointDefect_eq_half_sum] at hbound
    linarith



















end ExtendedLineGame

end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/ExtendedLineGame/MixedLinePointRejection.lean. -/
/-!
# Mixed line/point rejection bounds for the extended direct game

This module identifies the remaining reversed point/diagonal-line branch with
its completed line-point defect and bounds the sum of all four mixed
line/point rejection probabilities. These are exact supplied-witness
consequences used before the soundness step in the proof of `lem:qld-4-7`;
they do not establish a complete passing-value bound or construct a witness.

## References

- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1279-1288`
- Blueprint `lem:qld-4-7`.
- Issues #302, #305, #307, #309, and #311.
-/

@[expose] public section

open scoped BigOperators MatrixOrder ComplexOrder

-- The six-register products use the same instance-search budget as StateTransport.
set_option synthInstance.maxSize 400

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

namespace ExtendedLineGame

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {epsilon deltaQ deltaL : ℝ}
variable {setting : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon}
variable {points : _root_.MIPStarRE.QPBT.CombinedPointsWitness setting deltaQ}













/-- The sum of the four mixed point/line rejection probabilities is at most
`4 * deltaL`. This combines only the exact branch identities with the two
oriented completed-defect bounds supplied by `lines`. Paper
`14_analysis_of_the_pauli_basis_test.tex:1279-1288`; blueprint `lem:qld-4-7`. -/
theorem mixed_line_point_rejections_le_four_mul
    (lines : _root_.MIPStarRE.QPBT.ExtendedLinesWitness setting points deltaL) :
    _root_.MIPStarRE.QPBT.directLdBranchRejectionProbability P.extendedDirectLd (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
          (.aline, .point) +
        _root_.MIPStarRE.QPBT.directLdBranchRejectionProbability P.extendedDirectLd (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
          (.dline, .point) +
        _root_.MIPStarRE.QPBT.directLdBranchRejectionProbability P.extendedDirectLd (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
          (.point, .aline) +
        _root_.MIPStarRE.QPBT.directLdBranchRejectionProbability P.extendedDirectLd (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
          (.point, .dline) ≤ 4 * deltaL := by
  rw [_root_.MIPStarRE.QPBT.ExtendedLineGame.aline_point_rejection_eq_completedLinePointDefect lines,
    _root_.MIPStarRE.QPBT.ExtendedLineGame.dline_point_rejection_eq_completedLinePointDefect lines,
    _root_.MIPStarRE.QPBT.ExtendedLineGame.point_aline_rejection_eq_completedLinePointDefect lines,
    _root_.MIPStarRE.QPBT.ExtendedLineGame.point_dline_rejection_eq_completedLinePointDefect lines]
  have hbounds := _root_.MIPStarRE.QPBT.ExtendedLineGame.completedLinePointDefect_sums_le lines
  linarith [hbounds.1, hbounds.2]

end ExtendedLineGame

end

end MIPStarRE.QPBT

/-!
# Passing value of the supplied extended-line strategy

This module assembles the seven potentially rejecting branches of the directly
indexed low-degree strategy constructed from an `ExtendedLinesWitness`.  It
then transports the resulting lower bound through the explicit Naimark
dilation.  These are formalization-only supplied-witness consequences; they do
not construct the witness or establish source theorem `lem:qld-4-7`.

## References

- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1020-1034`
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1279-1288`
- Blueprint `lem:qld-4-7`
- Issue Dengnifer/MIPStarRE-QPBT-bak#348
-/



open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement



open MIPStarRE.QPBT.ExtendedLineGame

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {epsilon deltaQ deltaL : Real}
variable {setting : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon}
variable {points : _root_.MIPStarRE.QPBT.CombinedPointsWitness setting deltaQ}

theorem solution
    (lines : _root_.MIPStarRE.QPBT.ExtendedLinesWitness setting points deltaL) :
    _root_.MIPStarRE.QPBT.directLdBranchRejectionProbability P.extendedDirectLd (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
          (.point, .point) +
        _root_.MIPStarRE.QPBT.directLdBranchRejectionProbability P.extendedDirectLd (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
          (.point, .aline) +
        _root_.MIPStarRE.QPBT.directLdBranchRejectionProbability P.extendedDirectLd (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
          (.point, .dline) +
        _root_.MIPStarRE.QPBT.directLdBranchRejectionProbability P.extendedDirectLd (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
          (.aline, .point) +
        _root_.MIPStarRE.QPBT.directLdBranchRejectionProbability P.extendedDirectLd (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
          (.aline, .aline) +
        _root_.MIPStarRE.QPBT.directLdBranchRejectionProbability P.extendedDirectLd (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
          (.dline, .point) +
        _root_.MIPStarRE.QPBT.directLdBranchRejectionProbability P.extendedDirectLd (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
          (.dline, .dline) ≤
      deltaQ + 16 * deltaL + 4 * Real.sqrt (deltaQ + 2 * deltaL) +
        5 * ((P.m * P.d : Real) / (P.q : Real)) := by
  have hpoint := _root_.MIPStarRE.QPBT.ExtendedLineGame.point_point_rejection_le lines
  have hmixed := _root_.MIPStarRE.QPBT.ExtendedLineGame.mixed_line_point_rejections_le_four_mul lines
  have haxis :=
    _root_.MIPStarRE.QPBT.ExtendedLineGame.aline_aline_rejection_le_axisParameterEvaluatedCoefficientDefect_add lines
  have hdiagonal :=
    _root_.MIPStarRE.QPBT.ExtendedLineGame.dline_dline_rejection_le_diagonalParameterEvaluatedCoefficientDefect_add lines
  rw [_root_.MIPStarRE.QPBT.ExtendedLineGame.axis_parameter_evaluated_coefficient_defect_eq] at haxis
  rw [_root_.MIPStarRE.QPBT.ExtendedLineGame.diagonal_parameter_evaluated_coefficient_defect_eq] at hdiagonal
  have haxisEval := _root_.MIPStarRE.QPBT.ExtendedLineGame.axis_parameter_evaluation_defect_le lines
  have hdiagonalEval := _root_.MIPStarRE.QPBT.ExtendedLineGame.diagonal_parameter_evaluation_defect_le lines
  have hcollision :
      (P.d : Real) / (P.extendedDirectLd.q : Real) +
          (P.extendedDirectLd.m * P.extendedDirectLd.d : Real) /
            (P.extendedDirectLd.q : Real) ≤
        5 * ((P.m * P.d : Real) / (P.q : Real)) := by
    calc
      _ = ((P.extendedDirectLd.d : Real) +
            (P.extendedDirectLd.m * P.extendedDirectLd.d : Real)) /
          (P.extendedDirectLd.q : Real) := by
        change
          (P.extendedDirectLd.d : Real) / (P.extendedDirectLd.q : Real) +
              (P.extendedDirectLd.m * P.extendedDirectLd.d : Real) /
                (P.extendedDirectLd.q : Real) = _
        ring
      _ ≤ _ := _root_.MIPStarRE.QPBT.extendedDirectLd_coefficientCollisionLoss_le_five_mul P
  linarith
