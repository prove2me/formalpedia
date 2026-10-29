-- Prove2me | solution 1 for MIPStarRE.QPBT.ExtendedLineGame.axis_parameter_evaluation_defect_le
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T02:27:10.65615+00:00
-- url     : https://prove2.me/submissions/4f8a506b-bf2d-454d-ab52-083df1bb9151

-- Generated proof for MIPStarRE.QPBT.ExtendedLineGame.axis_parameter_evaluation_defect_le.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
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
import Definitions.Def_QPBT_QPBT_Algebra_Coefficients
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_Lines
import Definitions.Def_QPBT_QPBT_Algebra_LowDegreeCode
import Definitions.Def_QPBT_QPBT_Combining_Defs
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Game
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_GameValue
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_BranchComparison
import Definitions.Def_QPBT_QPBT_Combining_ExtendedLineGame
import Definitions.Def_QPBT_QPBT_Combining_ExtendedLineGame_EvaluatedLineComparison
import Definitions.Def_QPBT_QPBT_Combining_ExtendedLineGame_LineNoneMass
import Definitions.Def_QPBT_QPBT_Combining_ExtendedLineGame_LinePointRejection
import Definitions.Def_QPBT_QPBT_Combining_ExtendedLineGame_ParameterCompletion
import Definitions.Def_QPBT_QPBT_Combining_ExtendedLineGame_ParameterEvaluatedLineBound
import Definitions.Def_QPBT_QPBT_Combining_Witnesses
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistributionAux
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_Observables_LineDefs
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_MIPStarRE_QPBT_ExtendedLineGame_aline_point_rejection_eq_completedLinePointDefect
import Theorems.Thm_MIPStarRE_QPBT_ExtendedLineGame_axis_same_line_evaluation_defect_le
import Theorems.Thm_MIPStarRE_QPBT_ExtendedLineGame_directEvalOpt_eq_some_iff
import Theorems.Thm_MIPStarRE_QPBT_ExtendedLineGame_dline_point_rejection_eq_completedLinePointDefect
import Theorems.Thm_MIPStarRE_QPBT_ExtendedLineGame_outcomeWeight_eq_zero_of_invalid
import Theorems.Thm_MIPStarRE_QPBT_ExtendedLineGame_parameterEvalDefect_le_completed_add_none
import Theorems.Thm_MIPStarRE_QPBT_ExtendedLineGame_point_aline_rejection_eq_completedLinePointDefect
import Theorems.Thm_MIPStarRE_QPBT_ExtendedLineGame_point_dline_rejection_eq_completedLinePointDefect
import Theorems.Thm_MIPStarRE_QPBT_WinImplications_avgOver_mix
import Theorems.Thm_MIPStarRE_QPBT_WinImplications_consistencyDefect_postprocess_eq_mismatch
import Theorems.Thm_MIPStarRE_QPBT_avgOver_directALinePointDist_resample
import Theorems.Thm_MIPStarRE_QPBT_directLdBranchRejectionProbability_nonneg
import Theorems.Thm_MIPStarRE_QPBT_outcome_event_weight_mono
import Theorems.Thm_MIPStarRE_QPBT_sum_outcome_weight_left
import Theorems.Thm_MIPStarRE_QPBT_sum_outcome_weight_right

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.ExtendedLineGame
end MIPStarRE.QPBT.ExtendedLineGame

/- Source helpers from QPBT/Combining/DirectLowDegree/Transport/BranchComparison.lean. -/
/-!
# Branch comparison for the coordinate strategies of the direct low-degree game

Every branch of the low individual degree failure probability of a coordinate
strategy `directCoordinateProjStrat` is compared with the ordered type-pair
branch of the direct game asking the same questions.  An accepted direct
answer pair reads out to equal LDT answers: the line answer, rebased to the
LDT line and evaluated at the LDT base point, is the point answer, and the
zero-direction convention reads the constant value at the base point.  Hence
the LDT inconsistency mass at a question pair is at most the rejected direct
Born mass there.  The point-agreement and axis-line branches then compare
exactly after the coordinate reindexing of `directPointEquiv`; the diagonal
branches are treated in `Transport.DiagonalRecursion`.

## References

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:214-458`
- `references/ldt-paper/test_definition.tex:130-151`
- Blueprint `def:ld-question-distribution`, `lem:ld-aline-level`,
  `lem:ld-dline-level`, `lem:ld-question-typed-cl`, `lem:alnf`, `lem:dlnf`,
  `def:ld-win-predicate`, `rem:ld-win-zero-direction`, and `def:ld-meas`
- `MIPStarRE/LDT/Test/StrategyFailures.lean:18-130`
- `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`
-/

@[expose] public section

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.Quantum

noncomputable section



/-! ## Rejected Born mass at a fixed question pair -/





/-- The branch rejection probability of an ordered type pair is the uniform
average of the rejected Born mass at the canonical questions of the common
direct sample. -/
theorem directLdBranchRejectionProbability_eq_avgOver (D : _root_.MIPStarRE.QPBT.DirectLdParams)
    (S : _root_.MIPStarRE.QPBT.Strategy (_root_.MIPStarRE.QPBT.directLdGame D)) (types : _root_.MIPStarRE.QPBT.LdType × _root_.MIPStarRE.QPBT.LdType) :
    _root_.MIPStarRE.QPBT.directLdBranchRejectionProbability D S types =
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.DirectLdSpace D)) fun sample =>
        _root_.MIPStarRE.QPBT.directRejectedMass D S
          (types.1, _root_.MIPStarRE.QPBT.directLdMap D types.1 sample)
          (types.2, _root_.MIPStarRE.QPBT.directLdMap D types.2 sample) :=
  rfl



/-! ## Accepted answer pairs read out consistently

An accepted answer pair of the direct game consists of well-formed answers
satisfying the line-versus-point clause or the consistency clause of
`def:ld-win-predicate`.  The readouts of `Transport.Questions` evaluate the
rebased line polynomial at the LDT base point, which is the direct point
at the canonical rebase parameter; the accepted clause forces this value to
be the point answer.  Zero directions use the constant readout at the base
point, where the universal clause of `rem:ld-win-zero-direction` gives the
value at parameter zero. -/















/-! ## Direct samples as products -/



/-! ## The point-agreement and axis-line branches -/



end

end MIPStarRE.QPBT

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

/- Source helpers from QPBT/Combining/ExtendedLineGame/LinePointRejection.lean. -/
/-!
# Line/point rejection for the extended direct game

This module identifies the axis-line/point, diagonal-line/point, and reversed
point/axis-line branch rejections of the strategy constructed from an
`ExtendedLinesWitness` with the corresponding completed line-point defects.
These are finite postprocessing and state-transport steps in the first
paragraph of the proof of `lem:qld-4-7`; they do not establish a passing-value
bound or construct the supplied witness.

## References

- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1279-1288`
- Blueprint `lem:qld-4-7`.
- Issues #302, #305, #307, and #309.
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







private theorem axis_point_win_iff_read_eq
    (sample : _root_.MIPStarRE.QPBT.DirectLdSpace P.extendedDirectLd)
    (coeffs : Fin P.extendedDirectLd.k →
      Fin (P.extendedDirectLd.d + 1) → _root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd)
    (values : Fin P.extendedDirectLd.k → _root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd) :
    _root_.MIPStarRE.QPBT.directLdWinPredicate P.extendedDirectLd
        (.aline, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .aline sample)
        (.point, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .point sample)
        (.alinePolys coeffs) (.pointVals values) = true ↔
      _root_.MIPStarRE.QPBT.ExtendedLineGame.axisGameRead sample (.alinePolys coeffs) = _root_.MIPStarRE.QPBT.ExtendedLineGame.pointGameRead (.pointVals values) := by
  let line := _root_.MIPStarRE.QPBT.directALineDescOf P.extendedDirectLd sample
  have hmem : sample.point ∈ line.pointSet := by
    simpa [line, _root_.MIPStarRE.QPBT.DirectLineDesc.pointSet, _root_.MIPStarRE.QPBT.directALineDescOf,
      _root_.MIPStarRE.QPBT.DirectLineDesc.base, _root_.MIPStarRE.QPBT.DirectLineDesc.direction] using
      (_root_.MIPStarRE.QPBT.mem_linePoints_lineRepMap (_root_.MIPStarRE.QPBT.coordinateDirection sample.index) sample.point)
  constructor
  · intro hwin
    have heval : _root_.MIPStarRE.QPBT.DirectEvaluatesTo line (coeffs _root_.MIPStarRE.QPBT.ExtendedLineGame.onlyCoordinate) sample.point
        (values _root_.MIPStarRE.QPBT.ExtendedLineGame.onlyCoordinate) := by
      refine ⟨hmem, ?_⟩
      intro parameter hparameter
      have hcondition : _root_.MIPStarRE.QPBT.directAlinePointCondition P.extendedDirectLd
          (_root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .aline sample)
          (_root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .point sample) coeffs values := by
        simpa [_root_.MIPStarRE.QPBT.directLdWinPredicate, _root_.MIPStarRE.QPBT.validDirectLdAnswer] using hwin
      exact hcondition parameter (by
        simpa [line, _root_.MIPStarRE.QPBT.directALineDescOf, _root_.MIPStarRE.QPBT.directLdMap, _root_.MIPStarRE.QPBT.DirectLineDesc.base,
          _root_.MIPStarRE.QPBT.DirectLineDesc.direction] using hparameter) _root_.MIPStarRE.QPBT.ExtendedLineGame.onlyCoordinate
    have hopt : _root_.MIPStarRE.QPBT.directEvalOpt line sample.point (coeffs _root_.MIPStarRE.QPBT.ExtendedLineGame.onlyCoordinate) =
        some (values _root_.MIPStarRE.QPBT.ExtendedLineGame.onlyCoordinate) :=
      (_root_.MIPStarRE.QPBT.ExtendedLineGame.directEvalOpt_eq_some_iff line sample.point (coeffs _root_.MIPStarRE.QPBT.ExtendedLineGame.onlyCoordinate)
        (values _root_.MIPStarRE.QPBT.ExtendedLineGame.onlyCoordinate)).2 heval
    simp [_root_.MIPStarRE.QPBT.ExtendedLineGame.axisGameRead, _root_.MIPStarRE.QPBT.ExtendedLineGame.pointGameRead, line, hopt]
  · intro hread
    have hopt : _root_.MIPStarRE.QPBT.directEvalOpt line sample.point (coeffs _root_.MIPStarRE.QPBT.ExtendedLineGame.onlyCoordinate) =
        some (values _root_.MIPStarRE.QPBT.ExtendedLineGame.onlyCoordinate) := by
      cases h : _root_.MIPStarRE.QPBT.directEvalOpt line sample.point (coeffs _root_.MIPStarRE.QPBT.ExtendedLineGame.onlyCoordinate) with
      | none => simp [_root_.MIPStarRE.QPBT.ExtendedLineGame.axisGameRead, _root_.MIPStarRE.QPBT.ExtendedLineGame.pointGameRead, line, h] at hread
      | some value =>
          have hvalue : value = values _root_.MIPStarRE.QPBT.ExtendedLineGame.onlyCoordinate := by
            apply (_root_.MIPStarRE.QPBT.extendedDirectScalarEquiv P).injective
            simpa [_root_.MIPStarRE.QPBT.ExtendedLineGame.axisGameRead, _root_.MIPStarRE.QPBT.ExtendedLineGame.pointGameRead, line, h] using hread
          subst value
          rfl
    have heval := (_root_.MIPStarRE.QPBT.ExtendedLineGame.directEvalOpt_eq_some_iff line sample.point
      (coeffs _root_.MIPStarRE.QPBT.ExtendedLineGame.onlyCoordinate) (values _root_.MIPStarRE.QPBT.ExtendedLineGame.onlyCoordinate)).1 hopt
    simp only [_root_.MIPStarRE.QPBT.directLdWinPredicate, _root_.MIPStarRE.QPBT.validDirectLdAnswer, Bool.and_self,
      ↓reduceIte, decide_eq_true_eq]
    intro parameter hparameter index
    have hindex : index = _root_.MIPStarRE.QPBT.ExtendedLineGame.onlyCoordinate := by
      have hlt : index.val < 1 := by
        exact index.isLt
      have hzero : (_root_.MIPStarRE.QPBT.ExtendedLineGame.onlyCoordinate (P := P)).val = 0 := rfl
      apply Fin.ext
      rw [hzero]
      omega
    subst index
    exact heval.2 parameter (by
      simpa [line, _root_.MIPStarRE.QPBT.directALineDescOf, _root_.MIPStarRE.QPBT.directLdMap, _root_.MIPStarRE.QPBT.DirectLineDesc.base,
        _root_.MIPStarRE.QPBT.DirectLineDesc.direction] using hparameter)







private theorem rejectedTerm_eq_read_mismatch
    (lines : _root_.MIPStarRE.QPBT.ExtendedLinesWitness setting points deltaL)
    (sample : _root_.MIPStarRE.QPBT.DirectLdSpace P.extendedDirectLd)
    (answerA answerB : _root_.MIPStarRE.QPBT.DirectLdAnswer P.extendedDirectLd) :
    (if _root_.MIPStarRE.QPBT.directLdWinPredicate P.extendedDirectLd
        (.aline, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .aline sample)
        (.point, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .point sample) answerA answerB then
      0
    else _root_.MIPStarRE.QPBT.outcomeWeight (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
      (.aline, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .aline sample)
      (.point, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .point sample) answerA answerB) =
      if _root_.MIPStarRE.QPBT.ExtendedLineGame.axisGameRead sample answerA = _root_.MIPStarRE.QPBT.ExtendedLineGame.pointGameRead answerB then 0
      else _root_.MIPStarRE.QPBT.outcomeWeight (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
        (.aline, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .aline sample)
        (.point, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .point sample) answerA answerB := by
  classical
  cases answerA with
  | pointVals valuesA =>
      cases answerB with
      | pointVals valuesB =>
          rw [_root_.MIPStarRE.QPBT.ExtendedLineGame.outcomeWeight_eq_zero_of_invalid lines _ _ _ _ (Or.inl rfl)]
          simp
      | alinePolys coeffsB =>
          rw [_root_.MIPStarRE.QPBT.ExtendedLineGame.outcomeWeight_eq_zero_of_invalid lines _ _ _ _ (Or.inl rfl)]
          simp
      | dlinePolys coeffsB =>
          rw [_root_.MIPStarRE.QPBT.ExtendedLineGame.outcomeWeight_eq_zero_of_invalid lines _ _ _ _ (Or.inl rfl)]
          simp
  | alinePolys coeffs =>
      cases answerB with
      | pointVals values =>
          by_cases hwin : _root_.MIPStarRE.QPBT.directLdWinPredicate P.extendedDirectLd
              (.aline, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .aline sample)
              (.point, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .point sample)
              (.alinePolys coeffs) (.pointVals values) = true
          · have hread := (axis_point_win_iff_read_eq sample coeffs values).1 hwin
            simp [hwin, hread]
          · have hread : _root_.MIPStarRE.QPBT.ExtendedLineGame.axisGameRead sample (.alinePolys coeffs) ≠
                _root_.MIPStarRE.QPBT.ExtendedLineGame.pointGameRead (.pointVals values) :=
              fun h => hwin ((axis_point_win_iff_read_eq sample coeffs values).2 h)
            simp [hwin, hread]
      | alinePolys coeffsB =>
          rw [_root_.MIPStarRE.QPBT.ExtendedLineGame.outcomeWeight_eq_zero_of_invalid lines _ _ _ _ (Or.inr rfl)]
          simp
      | dlinePolys coeffsB =>
          rw [_root_.MIPStarRE.QPBT.ExtendedLineGame.outcomeWeight_eq_zero_of_invalid lines _ _ _ _ (Or.inr rfl)]
          simp
  | dlinePolys coeffsA =>
      cases answerB with
      | pointVals valuesB =>
          rw [_root_.MIPStarRE.QPBT.ExtendedLineGame.outcomeWeight_eq_zero_of_invalid lines _ _ _ _ (Or.inl rfl)]
          simp
      | alinePolys coeffsB =>
          rw [_root_.MIPStarRE.QPBT.ExtendedLineGame.outcomeWeight_eq_zero_of_invalid lines _ _ _ _ (Or.inl rfl)]
          simp
      | dlinePolys coeffsB =>
          rw [_root_.MIPStarRE.QPBT.ExtendedLineGame.outcomeWeight_eq_zero_of_invalid lines _ _ _ _ (Or.inl rfl)]
          simp

/-- Fixed-sample axis-line/point rejection equals completed-read mismatch mass. -/
theorem rejectedMass_eq_read_mismatch
    (lines : _root_.MIPStarRE.QPBT.ExtendedLinesWitness setting points deltaL)
    (sample : _root_.MIPStarRE.QPBT.DirectLdSpace P.extendedDirectLd) :
    _root_.MIPStarRE.QPBT.directRejectedMass P.extendedDirectLd (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
        (.aline, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .aline sample)
        (.point, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .point sample) =
      _root_.MIPStarRE.QPBT.outcomeEventWeight (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
        (.aline, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .aline sample)
        (.point, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .point sample)
        (fun answerA answerB => _root_.MIPStarRE.QPBT.ExtendedLineGame.axisGameRead sample answerA ≠ _root_.MIPStarRE.QPBT.ExtendedLineGame.pointGameRead answerB) := by
  classical
  unfold _root_.MIPStarRE.QPBT.directRejectedMass _root_.MIPStarRE.QPBT.outcomeEventWeight
  apply Finset.sum_congr rfl
  intro answerA _
  apply Finset.sum_congr rfl
  intro answerB _
  have hterm := rejectedTerm_eq_read_mismatch lines sample answerA answerB
  by_cases hread : _root_.MIPStarRE.QPBT.ExtendedLineGame.axisGameRead sample answerA = _root_.MIPStarRE.QPBT.ExtendedLineGame.pointGameRead answerB
  · simpa [hread] using hterm
  · simpa [hread] using hterm





















private theorem point_axis_win_iff_read_eq
    (sample : _root_.MIPStarRE.QPBT.DirectLdSpace P.extendedDirectLd)
    (values : Fin P.extendedDirectLd.k → _root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd)
    (coeffs : Fin P.extendedDirectLd.k →
      Fin (P.extendedDirectLd.d + 1) → _root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd) :
    _root_.MIPStarRE.QPBT.directLdWinPredicate P.extendedDirectLd
        (.point, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .point sample)
        (.aline, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .aline sample)
        (.pointVals values) (.alinePolys coeffs) = true ↔
      _root_.MIPStarRE.QPBT.ExtendedLineGame.pointGameRead (.pointVals values) = _root_.MIPStarRE.QPBT.ExtendedLineGame.axisGameRead sample (.alinePolys coeffs) := by
  have hpredicate :
      _root_.MIPStarRE.QPBT.directLdWinPredicate P.extendedDirectLd
          (.point, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .point sample)
          (.aline, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .aline sample)
          (.pointVals values) (.alinePolys coeffs) =
        _root_.MIPStarRE.QPBT.directLdWinPredicate P.extendedDirectLd
          (.aline, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .aline sample)
          (.point, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .point sample)
          (.alinePolys coeffs) (.pointVals values) := by
    rfl
  rw [hpredicate]
  constructor
  · exact fun h => ((axis_point_win_iff_read_eq (P := P) sample coeffs values).1 h).symm
  · exact fun h =>
      (axis_point_win_iff_read_eq (P := P) sample coeffs values).2 h.symm







private theorem point_axis_rejectedTerm_eq_read_mismatch
    (lines : _root_.MIPStarRE.QPBT.ExtendedLinesWitness setting points deltaL)
    (sample : _root_.MIPStarRE.QPBT.DirectLdSpace P.extendedDirectLd)
    (answerA answerB : _root_.MIPStarRE.QPBT.DirectLdAnswer P.extendedDirectLd) :
    (if _root_.MIPStarRE.QPBT.directLdWinPredicate P.extendedDirectLd
        (.point, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .point sample)
        (.aline, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .aline sample) answerA answerB then
      0
    else _root_.MIPStarRE.QPBT.outcomeWeight (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
      (.point, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .point sample)
      (.aline, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .aline sample) answerA answerB) =
      if _root_.MIPStarRE.QPBT.ExtendedLineGame.pointGameRead answerA = _root_.MIPStarRE.QPBT.ExtendedLineGame.axisGameRead sample answerB then 0
      else _root_.MIPStarRE.QPBT.outcomeWeight (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
        (.point, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .point sample)
        (.aline, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .aline sample) answerA answerB := by
  classical
  cases answerA with
  | pointVals values =>
      cases answerB with
      | pointVals valuesB =>
          rw [_root_.MIPStarRE.QPBT.ExtendedLineGame.outcomeWeight_eq_zero_of_invalid lines _ _ _ _ (Or.inr rfl)]
          simp
      | alinePolys coeffs =>
          by_cases hwin : _root_.MIPStarRE.QPBT.directLdWinPredicate P.extendedDirectLd
              (.point, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .point sample)
              (.aline, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .aline sample)
              (.pointVals values) (.alinePolys coeffs) = true
          · have hread := (point_axis_win_iff_read_eq sample values coeffs).1 hwin
            simp [hwin, hread]
          · have hread : _root_.MIPStarRE.QPBT.ExtendedLineGame.pointGameRead (.pointVals values) ≠
                _root_.MIPStarRE.QPBT.ExtendedLineGame.axisGameRead sample (.alinePolys coeffs) :=
              fun h => hwin ((point_axis_win_iff_read_eq sample values coeffs).2 h)
            simp [hwin, hread]
      | dlinePolys coeffsB =>
          rw [_root_.MIPStarRE.QPBT.ExtendedLineGame.outcomeWeight_eq_zero_of_invalid lines _ _ _ _ (Or.inr rfl)]
          simp
  | alinePolys coeffsA =>
      cases answerB with
      | pointVals valuesB =>
          rw [_root_.MIPStarRE.QPBT.ExtendedLineGame.outcomeWeight_eq_zero_of_invalid lines _ _ _ _ (Or.inl rfl)]
          simp
      | alinePolys coeffsB =>
          rw [_root_.MIPStarRE.QPBT.ExtendedLineGame.outcomeWeight_eq_zero_of_invalid lines _ _ _ _ (Or.inl rfl)]
          simp
      | dlinePolys coeffsB =>
          rw [_root_.MIPStarRE.QPBT.ExtendedLineGame.outcomeWeight_eq_zero_of_invalid lines _ _ _ _ (Or.inl rfl)]
          simp
  | dlinePolys coeffsA =>
      cases answerB with
      | pointVals valuesB =>
          rw [_root_.MIPStarRE.QPBT.ExtendedLineGame.outcomeWeight_eq_zero_of_invalid lines _ _ _ _ (Or.inl rfl)]
          simp
      | alinePolys coeffsB =>
          rw [_root_.MIPStarRE.QPBT.ExtendedLineGame.outcomeWeight_eq_zero_of_invalid lines _ _ _ _ (Or.inl rfl)]
          simp
      | dlinePolys coeffsB =>
          rw [_root_.MIPStarRE.QPBT.ExtendedLineGame.outcomeWeight_eq_zero_of_invalid lines _ _ _ _ (Or.inl rfl)]
          simp

/-- Fixed-sample point/axis-line rejection equals completed-read mismatch mass. -/
theorem point_axis_rejectedMass_eq_read_mismatch
    (lines : _root_.MIPStarRE.QPBT.ExtendedLinesWitness setting points deltaL)
    (sample : _root_.MIPStarRE.QPBT.DirectLdSpace P.extendedDirectLd) :
    _root_.MIPStarRE.QPBT.directRejectedMass P.extendedDirectLd (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
        (.point, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .point sample)
        (.aline, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .aline sample) =
      _root_.MIPStarRE.QPBT.outcomeEventWeight (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
        (.point, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .point sample)
        (.aline, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .aline sample)
        (fun answerA answerB => _root_.MIPStarRE.QPBT.ExtendedLineGame.pointGameRead answerA ≠ _root_.MIPStarRE.QPBT.ExtendedLineGame.axisGameRead sample answerB) := by
  classical
  unfold _root_.MIPStarRE.QPBT.directRejectedMass _root_.MIPStarRE.QPBT.outcomeEventWeight
  apply Finset.sum_congr rfl
  intro answerA _
  apply Finset.sum_congr rfl
  intro answerB _
  have hterm := point_axis_rejectedTerm_eq_read_mismatch lines sample answerA answerB
  by_cases hread : _root_.MIPStarRE.QPBT.ExtendedLineGame.pointGameRead answerA = _root_.MIPStarRE.QPBT.ExtendedLineGame.axisGameRead sample answerB
  · simpa [hread] using hterm
  · simpa [hread] using hterm







end ExtendedLineGame
end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Games/Defs.lean. -/
/-!
# Games, tensor-product strategies, and value

This file provides the finite game carrier used by the Pauli basis test.  Pure
states are vectors in `EuclideanSpace`, and POVMs use the project's matrix
`Measurement` structure.

## References

The source-facing nodes are blueprint `def:game`, `def:povm-conventions`,
`def:tensor-product-strategy`, and `def:tensor-product-value`.
The paper origin is `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:10-57`.
-/

@[expose] public section

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.Quantum



attribute [instance] _root_.MIPStarRE.QPBT.Game.questionAFintype _root_.MIPStarRE.QPBT.Game.questionBFintype
  _root_.MIPStarRE.QPBT.Game.answerAFintype _root_.MIPStarRE.QPBT.Game.answerBFintype _root_.MIPStarRE.QPBT.Game.questionADecidableEq
  _root_.MIPStarRE.QPBT.Game.questionBDecidableEq _root_.MIPStarRE.QPBT.Game.answerADecidableEq _root_.MIPStarRE.QPBT.Game.answerBDecidableEq









attribute [instance] _root_.MIPStarRE.QPBT.Strategy.ιAFintype _root_.MIPStarRE.QPBT.Strategy.ιBFintype
  _root_.MIPStarRE.QPBT.Strategy.ιADecidableEq _root_.MIPStarRE.QPBT.Strategy.ιBDecidableEq



/-! ### Algebra of the tensor placement

The shared tensor-placement API.  These identities are used both by the perfect
Magic Square strategy (blueprint `thm:ms-from-ac`) and by the rigidity transfer
step (blueprint `thm:ms-rigidity`), so they live
with the definition rather than in either development. -/





















/- The Euclidean linear map is the shared action used by the value and distance
functionals.  Keeping it at the Euclidean-space level avoids accidentally
using the function-space supremum norm of `Matrix.mulVec`. -/



























/-- An answer event depending only on Alice has its Alice marginal weight. -/
theorem outcome_event_weight_left_eq {G : _root_.MIPStarRE.QPBT.Game} (S : _root_.MIPStarRE.QPBT.Strategy G)
    (x : G.QuestionA) (y : G.QuestionB)
    (E : G.AnswerA → Prop) [DecidablePred E] :
    _root_.MIPStarRE.QPBT.outcomeEventWeight S x y (fun a _ => E a) = _root_.MIPStarRE.QPBT.aliceEventWeight S x E := by
  unfold _root_.MIPStarRE.QPBT.outcomeEventWeight _root_.MIPStarRE.QPBT.aliceEventWeight
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : E a
  · simp [ha, _root_.MIPStarRE.QPBT.sum_outcome_weight_right S x y a]
  · simp [ha]

/-- An answer event depending only on Bob has its Bob marginal weight. -/
theorem outcome_event_weight_right_eq {G : _root_.MIPStarRE.QPBT.Game} (S : _root_.MIPStarRE.QPBT.Strategy G)
    (x : G.QuestionA) (y : G.QuestionB)
    (E : G.AnswerB → Prop) [DecidablePred E] :
    _root_.MIPStarRE.QPBT.outcomeEventWeight S x y (fun _ b => E b) = _root_.MIPStarRE.QPBT.bobEventWeight S y E := by
  unfold _root_.MIPStarRE.QPBT.outcomeEventWeight _root_.MIPStarRE.QPBT.bobEventWeight
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hb : E b
  · simp [hb, _root_.MIPStarRE.QPBT.sum_outcome_weight_left S x y b]
  · simp [hb]










end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/ExtendedLineGame/LineNoneMass.lean. -/
/-!
# Failed completed line-evaluation mass

This module bounds the marginal Born mass of the `none` outcome of each
completed line read by the corresponding mixed line/point rejection branch.
Wrong-format point answers also read as `none`, so the proof first removes
those answer pairs using their zero Born weight and only then applies event
inclusion.

These statements concern completed `Option`-valued readouts. They do not
identify successful parameter evaluation or prove a coefficient-collision
bound.

## References

- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1279-1288`
- `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:232-248`
- Blueprint `lem:qld-4-7`.
- Issue Dengnifer/MIPStarRE-QPBT-bak#332.
-/

@[expose] public section

open scoped BigOperators MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

namespace ExtendedLineGame

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {epsilon deltaQ deltaL : ℝ}
variable {setting : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon}
variable {points : _root_.MIPStarRE.QPBT.CombinedPointsWitness setting deltaQ}

/-- A direct point answer has completed read `none` exactly when its answer
tag is invalid for a point question. -/
private theorem pointGameRead_eq_none_iff_invalid
    (answer : _root_.MIPStarRE.QPBT.DirectLdAnswer P.extendedDirectLd) :
    _root_.MIPStarRE.QPBT.ExtendedLineGame.pointGameRead answer = none ↔
      _root_.MIPStarRE.QPBT.validDirectLdAnswer (D := P.extendedDirectLd) .point answer = false := by
  cases answer <;> simp [_root_.MIPStarRE.QPBT.ExtendedLineGame.pointGameRead, _root_.MIPStarRE.QPBT.validDirectLdAnswer]

/-- After zero-weight invalid point answers are removed, Alice's line-`none`
event is the event that the line read is `none` and the point read is not. -/
private theorem alice_line_none_event_eq_point_some
    (lines : _root_.MIPStarRE.QPBT.ExtendedLinesWitness setting points deltaL)
    (kind : _root_.MIPStarRE.QPBT.LdType) (sample : _root_.MIPStarRE.QPBT.DirectLdSpace P.extendedDirectLd)
    (readLine : _root_.MIPStarRE.QPBT.DirectLdAnswer P.extendedDirectLd → Option (_root_.MIPStarRE.QPBT.PauliScalar P)) :
    _root_.MIPStarRE.QPBT.outcomeEventWeight (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
        (kind, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd kind sample)
        (.point, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .point sample)
        (fun answerA _ => readLine answerA = none) =
      _root_.MIPStarRE.QPBT.outcomeEventWeight (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
        (kind, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd kind sample)
        (.point, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .point sample)
        (fun answerA answerB =>
          readLine answerA = none ∧ _root_.MIPStarRE.QPBT.ExtendedLineGame.pointGameRead answerB ≠ none) := by
  classical
  unfold _root_.MIPStarRE.QPBT.outcomeEventWeight
  apply Finset.sum_congr rfl
  intro answerA _
  apply Finset.sum_congr rfl
  intro answerB _
  by_cases hline : readLine answerA = none
  · by_cases hpoint : _root_.MIPStarRE.QPBT.ExtendedLineGame.pointGameRead answerB = none
    · have hinvalid := (pointGameRead_eq_none_iff_invalid answerB).1 hpoint
      rw [_root_.MIPStarRE.QPBT.ExtendedLineGame.outcomeWeight_eq_zero_of_invalid lines _ _ answerA answerB (Or.inr hinvalid)]
      simp [hline, hpoint]
    · simp [hline, hpoint]
  · simp [hline]

/-- After zero-weight invalid point answers are removed, Bob's line-`none`
event is the event that the point read is not `none` and the line read is. -/
private theorem bob_line_none_event_eq_point_some
    (lines : _root_.MIPStarRE.QPBT.ExtendedLinesWitness setting points deltaL)
    (kind : _root_.MIPStarRE.QPBT.LdType) (sample : _root_.MIPStarRE.QPBT.DirectLdSpace P.extendedDirectLd)
    (readLine : _root_.MIPStarRE.QPBT.DirectLdAnswer P.extendedDirectLd → Option (_root_.MIPStarRE.QPBT.PauliScalar P)) :
    _root_.MIPStarRE.QPBT.outcomeEventWeight (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
        (.point, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .point sample)
        (kind, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd kind sample)
        (fun _ answerB => readLine answerB = none) =
      _root_.MIPStarRE.QPBT.outcomeEventWeight (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
        (.point, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .point sample)
        (kind, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd kind sample)
        (fun answerA answerB =>
          _root_.MIPStarRE.QPBT.ExtendedLineGame.pointGameRead answerA ≠ none ∧ readLine answerB = none) := by
  classical
  unfold _root_.MIPStarRE.QPBT.outcomeEventWeight
  apply Finset.sum_congr rfl
  intro answerA _
  apply Finset.sum_congr rfl
  intro answerB _
  by_cases hpoint : _root_.MIPStarRE.QPBT.ExtendedLineGame.pointGameRead answerA = none
  · have hinvalid := (pointGameRead_eq_none_iff_invalid answerA).1 hpoint
    rw [_root_.MIPStarRE.QPBT.ExtendedLineGame.outcomeWeight_eq_zero_of_invalid lines _ _ answerA answerB (Or.inl hinvalid)]
    simp [hpoint]
  · by_cases hline : readLine answerB = none
    · simp [hpoint, hline]
    · simp [hpoint, hline]









/-- At a fixed sample, Alice's failed completed axis evaluation is contained
in the axis-line/point rejection event after zero-mass invalid tags are removed. -/
private theorem axis_alice_none_mass_at_le_rejectedMass
    (lines : _root_.MIPStarRE.QPBT.ExtendedLinesWitness setting points deltaL)
    (sample : _root_.MIPStarRE.QPBT.DirectLdSpace P.extendedDirectLd) :
    _root_.MIPStarRE.QPBT.aliceEventWeight (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
        (.aline, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .aline sample)
        (fun answer => _root_.MIPStarRE.QPBT.ExtendedLineGame.axisGameRead sample answer = none) ≤
      _root_.MIPStarRE.QPBT.directRejectedMass P.extendedDirectLd (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
        (.aline, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .aline sample)
        (.point, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .point sample) := by
  calc
    _ = _root_.MIPStarRE.QPBT.outcomeEventWeight (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
        (.aline, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .aline sample)
        (.point, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .point sample)
        (fun answerA _ => _root_.MIPStarRE.QPBT.ExtendedLineGame.axisGameRead sample answerA = none) :=
      (_root_.MIPStarRE.QPBT.outcome_event_weight_left_eq _ _ _ _).symm
    _ = _root_.MIPStarRE.QPBT.outcomeEventWeight (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
        (.aline, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .aline sample)
        (.point, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .point sample)
        (fun answerA answerB => _root_.MIPStarRE.QPBT.ExtendedLineGame.axisGameRead sample answerA = none ∧
          _root_.MIPStarRE.QPBT.ExtendedLineGame.pointGameRead answerB ≠ none) :=
      alice_line_none_event_eq_point_some lines .aline sample (_root_.MIPStarRE.QPBT.ExtendedLineGame.axisGameRead sample)
    _ ≤ _root_.MIPStarRE.QPBT.outcomeEventWeight (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
        (.aline, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .aline sample)
        (.point, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .point sample)
        (fun answerA answerB => _root_.MIPStarRE.QPBT.ExtendedLineGame.axisGameRead sample answerA ≠ _root_.MIPStarRE.QPBT.ExtendedLineGame.pointGameRead answerB) := by
      apply _root_.MIPStarRE.QPBT.outcome_event_weight_mono
      intro answerA answerB hnone heq
      exact hnone.2 (heq.symm.trans hnone.1)
    _ = _ := (_root_.MIPStarRE.QPBT.ExtendedLineGame.rejectedMass_eq_read_mismatch lines sample).symm



/-- At a fixed sample, Bob's failed completed axis evaluation is contained in
the point/axis-line rejection event after zero-mass invalid tags are removed. -/
private theorem axis_bob_none_mass_at_le_rejectedMass
    (lines : _root_.MIPStarRE.QPBT.ExtendedLinesWitness setting points deltaL)
    (sample : _root_.MIPStarRE.QPBT.DirectLdSpace P.extendedDirectLd) :
    _root_.MIPStarRE.QPBT.bobEventWeight (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
        (.aline, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .aline sample)
        (fun answer => _root_.MIPStarRE.QPBT.ExtendedLineGame.axisGameRead sample answer = none) ≤
      _root_.MIPStarRE.QPBT.directRejectedMass P.extendedDirectLd (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
        (.point, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .point sample)
        (.aline, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .aline sample) := by
  calc
    _ = _root_.MIPStarRE.QPBT.outcomeEventWeight (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
        (.point, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .point sample)
        (.aline, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .aline sample)
        (fun _ answerB => _root_.MIPStarRE.QPBT.ExtendedLineGame.axisGameRead sample answerB = none) :=
      (_root_.MIPStarRE.QPBT.outcome_event_weight_right_eq _ _ _ _).symm
    _ = _root_.MIPStarRE.QPBT.outcomeEventWeight (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
        (.point, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .point sample)
        (.aline, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .aline sample)
        (fun answerA answerB => _root_.MIPStarRE.QPBT.ExtendedLineGame.pointGameRead answerA ≠ none ∧
          _root_.MIPStarRE.QPBT.ExtendedLineGame.axisGameRead sample answerB = none) :=
      bob_line_none_event_eq_point_some lines .aline sample (_root_.MIPStarRE.QPBT.ExtendedLineGame.axisGameRead sample)
    _ ≤ _root_.MIPStarRE.QPBT.outcomeEventWeight (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
        (.point, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .point sample)
        (.aline, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .aline sample)
        (fun answerA answerB => _root_.MIPStarRE.QPBT.ExtendedLineGame.pointGameRead answerA ≠ _root_.MIPStarRE.QPBT.ExtendedLineGame.axisGameRead sample answerB) := by
      apply _root_.MIPStarRE.QPBT.outcome_event_weight_mono
      intro answerA answerB hnone heq
      exact hnone.1 (heq.trans hnone.2)
    _ = _ := (_root_.MIPStarRE.QPBT.ExtendedLineGame.point_axis_rejectedMass_eq_read_mismatch lines sample).symm



/-- Alice's failed completed axis-evaluation mass is bounded by the
axis-line/point branch rejection probability. -/
theorem axis_alice_none_mass_le_rejection
    (lines : _root_.MIPStarRE.QPBT.ExtendedLinesWitness setting points deltaL) :
    _root_.MIPStarRE.QPBT.ExtendedLineGame.axisAliceNoneMass lines ≤
      _root_.MIPStarRE.QPBT.directLdBranchRejectionProbability P.extendedDirectLd (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
        (.aline, .point) := by
  unfold _root_.MIPStarRE.QPBT.ExtendedLineGame.axisAliceNoneMass
  rw [_root_.MIPStarRE.QPBT.directLdBranchRejectionProbability_eq_avgOver]
  apply _root_.LIDT.MIPStarRE.LDT.avgOver_mono
  exact axis_alice_none_mass_at_le_rejectedMass lines



/-- Bob's failed completed axis-evaluation mass is bounded by the
point/axis-line branch rejection probability. -/
theorem axis_bob_none_mass_le_rejection
    (lines : _root_.MIPStarRE.QPBT.ExtendedLinesWitness setting points deltaL) :
    _root_.MIPStarRE.QPBT.ExtendedLineGame.axisBobNoneMass lines ≤
      _root_.MIPStarRE.QPBT.directLdBranchRejectionProbability P.extendedDirectLd (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
        (.point, .aline) := by
  unfold _root_.MIPStarRE.QPBT.ExtendedLineGame.axisBobNoneMass
  rw [_root_.MIPStarRE.QPBT.directLdBranchRejectionProbability_eq_avgOver]
  apply _root_.LIDT.MIPStarRE.LDT.avgOver_mono
  exact axis_bob_none_mass_at_le_rejectedMass lines



end ExtendedLineGame

end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/ExtendedLineGame/ParameterEvaluatedLineBound.lean. -/
/-!
# Bounds for independently parameter-evaluated line answers

This module specializes the parameter/completed-read comparison to the axis
and diagonal measurements supplied by an `ExtendedLinesWitness`. The affine
parameter is sampled independently of the line. Affine resampling then
recovers the original joint line-point law, including zero directions.
The numerical estimates are formalization-only consequences of the supplied
point and line witnesses supporting the classical-game construction in the
proof of `lem:qld-4-7`.

## References

- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1020-1034`
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1279-1288`
- `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:295-311`
- Blueprint `lem:qld-4-7`.
- Issue Dengnifer/MIPStarRE-QPBT-bak#341.
-/

@[expose] public section

open scoped BigOperators MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

namespace ExtendedLineGame

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {epsilon deltaQ deltaL : ℝ}
variable {setting : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon}
variable {points : _root_.MIPStarRE.QPBT.CombinedPointsWitness setting deltaQ}



private theorem coordinate_eq_lineCoordinate (i : Fin P.extendedDirectLd.k) :
    i = _root_.MIPStarRE.QPBT.ExtendedLineGame.lineCoordinate (P := P) := by
  apply Fin.ext
  have hi := i.isLt
  change i.val < 1 at hi
  change i.val = 0
  omega













private theorem axisQuestion_directALineDescOf
    (sample : _root_.MIPStarRE.QPBT.DirectLdSpace P.extendedDirectLd) :
    _root_.MIPStarRE.QPBT.ExtendedLineGame.axisQuestion (_root_.MIPStarRE.QPBT.directALineDescOf P.extendedDirectLd sample) =
      (.aline, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .aline sample) := by
  rfl



private theorem axis_completed_mismatch_eq
    (lines : _root_.MIPStarRE.QPBT.ExtendedLinesWitness setting points deltaL)
    (sample : _root_.MIPStarRE.QPBT.DirectLdSpace P.extendedDirectLd) :
    _root_.MIPStarRE.QPBT.outcomeEventWeight (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
        (.aline, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .aline sample)
        (.aline, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .aline sample)
        (fun answerA answerB =>
          _root_.MIPStarRE.QPBT.directEvalOpt (_root_.MIPStarRE.QPBT.directALineDescOf P.extendedDirectLd sample) sample.point
              (_root_.MIPStarRE.QPBT.ExtendedLineGame.axisCoefficients answerA) ≠
            _root_.MIPStarRE.QPBT.directEvalOpt (_root_.MIPStarRE.QPBT.directALineDescOf P.extendedDirectLd sample) sample.point
              (_root_.MIPStarRE.QPBT.ExtendedLineGame.axisCoefficients answerB)) =
      _root_.MIPStarRE.QPBT.outcomeEventWeight (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
        (.aline, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .aline sample)
        (.aline, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .aline sample)
        (fun answerA answerB => _root_.MIPStarRE.QPBT.ExtendedLineGame.axisGameRead sample answerA ≠ _root_.MIPStarRE.QPBT.ExtendedLineGame.axisGameRead sample answerB) := by
  classical
  unfold _root_.MIPStarRE.QPBT.outcomeEventWeight
  apply Finset.sum_congr rfl
  intro answerA _
  apply Finset.sum_congr rfl
  intro answerB _
  by_cases hinvalid : _root_.MIPStarRE.QPBT.validDirectLdAnswer (D := P.extendedDirectLd) .aline answerA = false ∨
      _root_.MIPStarRE.QPBT.validDirectLdAnswer (D := P.extendedDirectLd) .aline answerB = false
  · rw [_root_.MIPStarRE.QPBT.ExtendedLineGame.outcomeWeight_eq_zero_of_invalid lines _ _ answerA answerB hinvalid]
    simp
  · cases answerA <;> cases answerB <;> simp [_root_.MIPStarRE.QPBT.validDirectLdAnswer] at hinvalid
    have hmap : Function.Injective (Option.map (_root_.MIPStarRE.QPBT.extendedDirectScalarEquiv P)) :=
      Option.map_injective (_root_.MIPStarRE.QPBT.extendedDirectScalarEquiv P).injective
    simp only [_root_.MIPStarRE.QPBT.ExtendedLineGame.axisCoefficients, _root_.MIPStarRE.QPBT.ExtendedLineGame.axisGameRead, coordinate_eq_lineCoordinate,
      ne_eq, hmap.eq_iff]
    rfl



private theorem axis_none_mass_eq
    (lines : _root_.MIPStarRE.QPBT.ExtendedLinesWitness setting points deltaL)
    (side : _root_.MIPStarRE.QPBT.PlayerSide) (sample : _root_.MIPStarRE.QPBT.DirectLdSpace P.extendedDirectLd) :
    (match side with
      | .alice => _root_.MIPStarRE.QPBT.aliceEventWeight (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
          (.aline, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .aline sample)
          (fun answer => _root_.MIPStarRE.QPBT.directEvalOpt (_root_.MIPStarRE.QPBT.directALineDescOf P.extendedDirectLd sample)
            sample.point (_root_.MIPStarRE.QPBT.ExtendedLineGame.axisCoefficients answer) = none)
      | .bob => _root_.MIPStarRE.QPBT.bobEventWeight (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
          (.aline, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .aline sample)
          (fun answer => _root_.MIPStarRE.QPBT.directEvalOpt (_root_.MIPStarRE.QPBT.directALineDescOf P.extendedDirectLd sample)
            sample.point (_root_.MIPStarRE.QPBT.ExtendedLineGame.axisCoefficients answer) = none)) =
    (match side with
      | .alice => _root_.MIPStarRE.QPBT.aliceEventWeight (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
          (.aline, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .aline sample)
          (fun answer => _root_.MIPStarRE.QPBT.ExtendedLineGame.axisGameRead sample answer = none)
      | .bob => _root_.MIPStarRE.QPBT.bobEventWeight (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
          (.aline, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .aline sample)
          (fun answer => _root_.MIPStarRE.QPBT.ExtendedLineGame.axisGameRead sample answer = none)) := by
  cases side <;> dsimp only
  all_goals first
  | rw [← _root_.MIPStarRE.QPBT.outcome_event_weight_left_eq (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
      (.aline, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .aline sample)
      (.aline, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .aline sample),
      ← _root_.MIPStarRE.QPBT.outcome_event_weight_left_eq (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
        (.aline, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .aline sample)
        (.aline, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .aline sample)]
  | rw [← _root_.MIPStarRE.QPBT.outcome_event_weight_right_eq (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
      (.aline, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .aline sample)
      (.aline, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .aline sample),
      ← _root_.MIPStarRE.QPBT.outcome_event_weight_right_eq (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
        (.aline, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .aline sample)
        (.aline, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .aline sample)]
  all_goals
    unfold _root_.MIPStarRE.QPBT.outcomeEventWeight
    apply Finset.sum_congr rfl
    intro answerA _
    apply Finset.sum_congr rfl
    intro answerB _
  · by_cases hinvalid : _root_.MIPStarRE.QPBT.validDirectLdAnswer (D := P.extendedDirectLd) .aline answerA = false
    · rw [_root_.MIPStarRE.QPBT.ExtendedLineGame.outcomeWeight_eq_zero_of_invalid lines _ _ answerA answerB (Or.inl hinvalid)]
      simp
    · cases answerA <;> simp [_root_.MIPStarRE.QPBT.validDirectLdAnswer] at hinvalid
      simp [_root_.MIPStarRE.QPBT.ExtendedLineGame.axisCoefficients, _root_.MIPStarRE.QPBT.ExtendedLineGame.axisGameRead, coordinate_eq_lineCoordinate]
      rfl
  · by_cases hinvalid : _root_.MIPStarRE.QPBT.validDirectLdAnswer (D := P.extendedDirectLd) .aline answerB = false
    · rw [_root_.MIPStarRE.QPBT.ExtendedLineGame.outcomeWeight_eq_zero_of_invalid lines _ _ answerA answerB (Or.inr hinvalid)]
      simp
    · cases answerB <;> simp [_root_.MIPStarRE.QPBT.validDirectLdAnswer] at hinvalid
      simp [_root_.MIPStarRE.QPBT.ExtendedLineGame.axisCoefficients, _root_.MIPStarRE.QPBT.ExtendedLineGame.axisGameRead, coordinate_eq_lineCoordinate]
      rfl



/-- Averaging the parameter/completed-read comparison over the actual axis law. -/
private theorem axis_parameter_evaluation_defect_le_completed
    (lines : _root_.MIPStarRE.QPBT.ExtendedLinesWitness setting points deltaL) :
    _root_.MIPStarRE.QPBT.ExtendedLineGame.axisParameterEvaluationDefect lines ≤
      _root_.MIPStarRE.QPBT.ExtendedLineGame.axisSameLineEvaluationDefect lines + _root_.MIPStarRE.QPBT.ExtendedLineGame.axisAliceNoneMass lines + _root_.MIPStarRE.QPBT.ExtendedLineGame.axisBobNoneMass lines := by
  let F : _root_.MIPStarRE.QPBT.DirectLineDesc P.extendedDirectLd ×
      (Fin P.extendedDirectLd.m → _root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd) → ℝ := fun sample =>
    _root_.MIPStarRE.QPBT.outcomeEventWeight (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines) (_root_.MIPStarRE.QPBT.ExtendedLineGame.axisQuestion sample.1) (_root_.MIPStarRE.QPBT.ExtendedLineGame.axisQuestion sample.1)
        (fun answerA answerB => _root_.MIPStarRE.QPBT.directEvalOpt sample.1 sample.2 (_root_.MIPStarRE.QPBT.ExtendedLineGame.axisCoefficients answerA) ≠
          _root_.MIPStarRE.QPBT.directEvalOpt sample.1 sample.2 (_root_.MIPStarRE.QPBT.ExtendedLineGame.axisCoefficients answerB)) +
      _root_.MIPStarRE.QPBT.aliceEventWeight (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines) (_root_.MIPStarRE.QPBT.ExtendedLineGame.axisQuestion sample.1)
        (fun answer => _root_.MIPStarRE.QPBT.directEvalOpt sample.1 sample.2 (_root_.MIPStarRE.QPBT.ExtendedLineGame.axisCoefficients answer) = none) +
      _root_.MIPStarRE.QPBT.bobEventWeight (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines) (_root_.MIPStarRE.QPBT.ExtendedLineGame.axisQuestion sample.1)
        (fun answer => _root_.MIPStarRE.QPBT.directEvalOpt sample.1 sample.2 (_root_.MIPStarRE.QPBT.ExtendedLineGame.axisCoefficients answer) = none)
  have havg : _root_.MIPStarRE.QPBT.ExtendedLineGame.axisParameterEvaluationDefect lines ≤
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.directALinePointDist P.extendedDirectLd) F := by
    rw [← _root_.MIPStarRE.QPBT.avgOver_directALinePointDist_resample P.extendedDirectLd F,
      _root_.LIDT.MIPStarRE.LDT.Distribution.avgOver_map]
    unfold _root_.MIPStarRE.QPBT.ExtendedLineGame.axisParameterEvaluationDefect
    apply _root_.LIDT.MIPStarRE.LDT.avgOver_mono
    intro sample
    apply _root_.LIDT.MIPStarRE.LDT.avgOver_mono
    intro parameter
    exact _root_.MIPStarRE.QPBT.ExtendedLineGame.parameterEvalDefect_le_completed_add_none
      (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines) (_root_.MIPStarRE.QPBT.ExtendedLineGame.axisQuestion sample.1) (_root_.MIPStarRE.QPBT.ExtendedLineGame.axisQuestion sample.1)
      _root_.MIPStarRE.QPBT.ExtendedLineGame.axisCoefficients _root_.MIPStarRE.QPBT.ExtendedLineGame.axisCoefficients sample.1 parameter
  calc
    _root_.MIPStarRE.QPBT.ExtendedLineGame.axisParameterEvaluationDefect lines ≤
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.directALinePointDist P.extendedDirectLd) F := havg
    _ = _root_.MIPStarRE.QPBT.ExtendedLineGame.axisSameLineEvaluationDefect lines + _root_.MIPStarRE.QPBT.ExtendedLineGame.axisAliceNoneMass lines +
        _root_.MIPStarRE.QPBT.ExtendedLineGame.axisBobNoneMass lines := by
      simp only [F, _root_.MIPStarRE.QPBT.directALinePointDist, _root_.LIDT.MIPStarRE.LDT.Distribution.avgOver_map,
        axisQuestion_directALineDescOf, axis_completed_mismatch_eq,
        axis_none_mass_eq lines .alice, axis_none_mass_eq lines .bob, _root_.LIDT.MIPStarRE.LDT.avgOver_add]
      change _ + _root_.MIPStarRE.QPBT.ExtendedLineGame.axisAliceNoneMass lines + _root_.MIPStarRE.QPBT.ExtendedLineGame.axisBobNoneMass lines =
        _root_.MIPStarRE.QPBT.ExtendedLineGame.axisSameLineEvaluationDefect lines + _root_.MIPStarRE.QPBT.ExtendedLineGame.axisAliceNoneMass lines + _root_.MIPStarRE.QPBT.ExtendedLineGame.axisBobNoneMass lines
      congr 2
      exact (_root_.MIPStarRE.QPBT.WinImplications.consistencyDefect_postprocess_eq_mismatch
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.DirectLdSpace P.extendedDirectLd)) (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
        (fun sample => (.aline, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .aline sample))
        (fun sample => (.aline, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .aline sample))
        _root_.MIPStarRE.QPBT.ExtendedLineGame.axisGameRead _root_.MIPStarRE.QPBT.ExtendedLineGame.axisGameRead).symm







end ExtendedLineGame

end

end MIPStarRE.QPBT

/-!
# Bounds for independently parameter-evaluated line answers

This module specializes the parameter/completed-read comparison to the axis
and diagonal measurements supplied by an `ExtendedLinesWitness`. The affine
parameter is sampled independently of the line. Affine resampling then
recovers the original joint line-point law, including zero directions.
The numerical estimates are formalization-only consequences of the supplied
point and line witnesses supporting the classical-game construction in the
proof of `lem:qld-4-7`.

## References

- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1020-1034`
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1279-1288`
- `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:295-311`
- Blueprint `lem:qld-4-7`.
- Issue Dengnifer/MIPStarRE-QPBT-bak#341.
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
    _root_.MIPStarRE.QPBT.ExtendedLineGame.axisParameterEvaluationDefect lines ≤
      6 * deltaL + 2 * Real.sqrt (deltaQ + 2 * deltaL) := by
  have hforward := (_root_.MIPStarRE.QPBT.ExtendedLineGame.completedLinePointDefect_sums_le lines).1
  rw [← _root_.MIPStarRE.QPBT.ExtendedLineGame.aline_point_rejection_eq_completedLinePointDefect lines,
    ← _root_.MIPStarRE.QPBT.ExtendedLineGame.dline_point_rejection_eq_completedLinePointDefect lines] at hforward
  have hreverse := (_root_.MIPStarRE.QPBT.ExtendedLineGame.completedLinePointDefect_sums_le lines).2
  rw [← _root_.MIPStarRE.QPBT.ExtendedLineGame.point_aline_rejection_eq_completedLinePointDefect lines,
    ← _root_.MIPStarRE.QPBT.ExtendedLineGame.point_dline_rejection_eq_completedLinePointDefect lines] at hreverse
  have hforwardNonneg := _root_.MIPStarRE.QPBT.directLdBranchRejectionProbability_nonneg
    P.extendedDirectLd (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines) (.dline, .point)
  have hreverseNonneg := _root_.MIPStarRE.QPBT.directLdBranchRejectionProbability_nonneg
    P.extendedDirectLd (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines) (.point, .dline)
  have hcomparison := _root_.MIPStarRE.QPBT.ExtendedLineGame.axis_same_line_evaluation_defect_le lines
  have hnoneA := _root_.MIPStarRE.QPBT.ExtendedLineGame.axis_alice_none_mass_le_rejection lines
  have hnoneB := _root_.MIPStarRE.QPBT.ExtendedLineGame.axis_bob_none_mass_le_rejection lines
  have hparameter := axis_parameter_evaluation_defect_le_completed lines
  linarith
