-- Prove2me | solution 1 for MIPStarRE.QPBT.ExtendedLineGame.point_aline_rejection_eq_completedLinePointDefect
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T02:13:28.981845+00:00
-- url     : https://prove2.me/submissions/ccbe1787-6db4-4d3b-90b8-581d8ef1c316

-- Generated proof for MIPStarRE.QPBT.ExtendedLineGame.point_aline_rejection_eq_completedLinePointDefect.
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
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Game
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_GameValue
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_BranchComparison
import Definitions.Def_QPBT_QPBT_Combining_ExtendedLineGame
import Definitions.Def_QPBT_QPBT_Combining_ExtendedLineGame_LinePointRejection
import Definitions.Def_QPBT_QPBT_Combining_Witnesses
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_Observables_LineDefs
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_MIPStarRE_QPBT_ExtendedLineGame_directEvalOpt_eq_some_iff
import Theorems.Thm_MIPStarRE_QPBT_ExtendedLineGame_outcomeWeight_eq_zero_of_invalid
import Theorems.Thm_MIPStarRE_QPBT_ExtendedLineGame_reversed_axis_completed_defect_eq_read_defect
import Theorems.Thm_MIPStarRE_QPBT_WinImplications_consistencyDefect_postprocess_eq_mismatch

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

open scoped BigOperators MatrixOrder ComplexOrder

-- The six-register products use the same instance-search budget as StateTransport.
set_option synthInstance.maxSize 400

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum



open MIPStarRE.QPBT.ExtendedLineGame

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {epsilon deltaQ deltaL : ℝ}
variable {setting : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon}
variable {points : _root_.MIPStarRE.QPBT.CombinedPointsWitness setting deltaQ}

theorem solution
    (lines : _root_.MIPStarRE.QPBT.ExtendedLinesWitness setting points deltaL) :
    _root_.MIPStarRE.QPBT.directLdBranchRejectionProbability P.extendedDirectLd (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
        (.point, .aline) =
      _root_.MIPStarRE.QPBT.ExtendedLineGame.completedLinePointDefect lines .BB' .AB''
        (_root_.MIPStarRE.QPBT.directALinePointDist P.extendedDirectLd) := by
  rw [_root_.MIPStarRE.QPBT.directLdBranchRejectionProbability_eq_avgOver]
  calc
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.DirectLdSpace P.extendedDirectLd))
        (fun sample => _root_.MIPStarRE.QPBT.directRejectedMass P.extendedDirectLd (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
          (.point, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .point sample)
          (.aline, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .aline sample)) =
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.DirectLdSpace P.extendedDirectLd))
          (fun sample => _root_.MIPStarRE.QPBT.outcomeEventWeight (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
            (.point, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .point sample)
            (.aline, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .aline sample)
            (fun answerA answerB =>
              _root_.MIPStarRE.QPBT.ExtendedLineGame.pointGameRead answerA ≠ _root_.MIPStarRE.QPBT.ExtendedLineGame.axisGameRead sample answerB)) := by
      apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
      exact _root_.MIPStarRE.QPBT.ExtendedLineGame.point_axis_rejectedMass_eq_read_mismatch lines
    _ = _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.DirectLdSpace P.extendedDirectLd))
        (fun sample answer => _root_.MIPStarRE.QPBT.heteroKron
          (((_root_.MIPStarRE.QPBT.ExtendedLineGame.answerMeasurement lines .alice
            (.point, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .point sample)).postprocess
              _root_.MIPStarRE.QPBT.ExtendedLineGame.pointGameRead).effect answer) 1)
        (fun sample answer => _root_.MIPStarRE.QPBT.heteroKron 1
          (((_root_.MIPStarRE.QPBT.ExtendedLineGame.answerMeasurement lines .bob
            (.aline, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .aline sample)).postprocess
              (_root_.MIPStarRE.QPBT.ExtendedLineGame.axisGameRead sample)).effect answer))
        (_root_.MIPStarRE.QPBT.ExtendedLineGame.pairState setting) := by
      exact (_root_.MIPStarRE.QPBT.WinImplications.consistencyDefect_postprocess_eq_mismatch
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.DirectLdSpace P.extendedDirectLd)) (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
        (fun sample => (.point, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .point sample))
        (fun sample => (.aline, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .aline sample))
        (fun _ => _root_.MIPStarRE.QPBT.ExtendedLineGame.pointGameRead) _root_.MIPStarRE.QPBT.ExtendedLineGame.axisGameRead).symm
    _ = _root_.MIPStarRE.QPBT.ExtendedLineGame.completedLinePointDefect lines .BB' .AB''
        (_root_.MIPStarRE.QPBT.directALinePointDist P.extendedDirectLd) :=
      (_root_.MIPStarRE.QPBT.ExtendedLineGame.reversed_axis_completed_defect_eq_read_defect lines).symm
