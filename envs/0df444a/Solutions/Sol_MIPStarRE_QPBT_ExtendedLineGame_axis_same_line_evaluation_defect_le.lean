-- Prove2me | solution 1 for MIPStarRE.QPBT.ExtendedLineGame.axis_same_line_evaluation_defect_le
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T02:22:38.616755+00:00
-- url     : https://prove2.me/submissions/0d895bd7-4f28-4022-a8d4-0ab7533e0454

-- Generated proof for MIPStarRE.QPBT.ExtendedLineGame.axis_same_line_evaluation_defect_le.
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
import Definitions.Def_QPBT_QPBT_Combining_ExtendedLineGame_EvaluatedLineComparison
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
import Theorems.Thm_MIPStarRE_QPBT_ExtendedLineGame_aline_point_rejection_eq_completedLinePointDefect
import Theorems.Thm_MIPStarRE_QPBT_ExtendedLineGame_axis_same_line_evaluation_defect_le_branch_chain
import Theorems.Thm_MIPStarRE_QPBT_ExtendedLineGame_dline_point_rejection_eq_completedLinePointDefect
import Theorems.Thm_MIPStarRE_QPBT_ExtendedLineGame_point_aline_rejection_eq_completedLinePointDefect
import Theorems.Thm_MIPStarRE_QPBT_ExtendedLineGame_point_dline_rejection_eq_completedLinePointDefect
import Theorems.Thm_MIPStarRE_QPBT_ExtendedLineGame_point_point_rejection_le
import Theorems.Thm_MIPStarRE_QPBT_WinImplications_avgOver_mix
import Theorems.Thm_MIPStarRE_QPBT_directLdBranchRejectionProbability_nonneg

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

/-!
# Completed same-line evaluation comparison

This module compares Alice's and Bob's completed axis-line or diagonal-line
readouts through the corresponding point readouts. The comparison uses the
consistency triangle on the common direct-game sample and then applies the
already proved mixed and point/point branch bounds.

The readouts take values in `Option (PauliScalar P)`. Agreement on `none`, in
particular for zero directions, is not an equality of parameter evaluations;
no coefficient-collision conclusion is asserted here.

## References

- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1279-1288`
- `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:389-401`
- Blueprint `lem:qld-4-7`.
- Issue Dengnifer/MIPStarRE-QPBT-bak#321.
-/



open scoped BigOperators MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum



open MIPStarRE.QPBT.ExtendedLineGame

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {epsilon deltaQ deltaL : ℝ}
variable {setting : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon}
variable {points : _root_.MIPStarRE.QPBT.CombinedPointsWitness setting deltaQ}

theorem solution
    (lines : _root_.MIPStarRE.QPBT.ExtendedLinesWitness setting points deltaL) :
    _root_.MIPStarRE.QPBT.ExtendedLineGame.axisSameLineEvaluationDefect lines ≤
      2 * deltaL + 2 * Real.sqrt (deltaQ + 2 * deltaL) := by
  have hforward := (_root_.MIPStarRE.QPBT.ExtendedLineGame.completedLinePointDefect_sums_le lines).1
  rw [← _root_.MIPStarRE.QPBT.ExtendedLineGame.aline_point_rejection_eq_completedLinePointDefect lines,
    ← _root_.MIPStarRE.QPBT.ExtendedLineGame.dline_point_rejection_eq_completedLinePointDefect lines] at hforward
  have hforwardNonneg := _root_.MIPStarRE.QPBT.directLdBranchRejectionProbability_nonneg
    P.extendedDirectLd (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines) (.dline, .point)
  have hforwardAxis :
      _root_.MIPStarRE.QPBT.directLdBranchRejectionProbability P.extendedDirectLd (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
          (.aline, .point) ≤ 2 * deltaL := by
    linarith
  have hreverse := (_root_.MIPStarRE.QPBT.ExtendedLineGame.completedLinePointDefect_sums_le lines).2
  rw [← _root_.MIPStarRE.QPBT.ExtendedLineGame.point_aline_rejection_eq_completedLinePointDefect lines,
    ← _root_.MIPStarRE.QPBT.ExtendedLineGame.point_dline_rejection_eq_completedLinePointDefect lines] at hreverse
  have hreverseNonneg := _root_.MIPStarRE.QPBT.directLdBranchRejectionProbability_nonneg
    P.extendedDirectLd (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines) (.point, .dline)
  have hreverseAxis :
      _root_.MIPStarRE.QPBT.directLdBranchRejectionProbability P.extendedDirectLd (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
          (.point, .aline) ≤ 2 * deltaL := by
    linarith
  have hpoint := _root_.MIPStarRE.QPBT.ExtendedLineGame.point_point_rejection_le lines
  calc
    _root_.MIPStarRE.QPBT.ExtendedLineGame.axisSameLineEvaluationDefect lines ≤
        _root_.MIPStarRE.QPBT.directLdBranchRejectionProbability P.extendedDirectLd (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
            (.aline, .point) +
          2 * Real.sqrt
            (_root_.MIPStarRE.QPBT.directLdBranchRejectionProbability P.extendedDirectLd (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
                (.point, .point) +
              _root_.MIPStarRE.QPBT.directLdBranchRejectionProbability P.extendedDirectLd (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
                (.point, .aline)) :=
      _root_.MIPStarRE.QPBT.ExtendedLineGame.axis_same_line_evaluation_defect_le_branch_chain lines
    _ ≤ 2 * deltaL +
        2 * Real.sqrt
          (_root_.MIPStarRE.QPBT.directLdBranchRejectionProbability P.extendedDirectLd (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
              (.point, .point) +
            _root_.MIPStarRE.QPBT.directLdBranchRejectionProbability P.extendedDirectLd (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
              (.point, .aline)) := by
      exact add_le_add hforwardAxis le_rfl
    _ ≤ 2 * deltaL + 2 * Real.sqrt (deltaQ + 2 * deltaL) := by
      gcongr
