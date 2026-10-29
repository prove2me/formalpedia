-- Prove2me | solution 1 for MIPStarRE.QPBT.ExtendedLineGame.dline_point_rejection_eq_completedLinePointDefect
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T02:13:28.552554+00:00
-- url     : https://prove2.me/submissions/a6aba50b-a241-41f0-9a3d-0d41fd21c1cc

-- Generated proof for MIPStarRE.QPBT.ExtendedLineGame.dline_point_rejection_eq_completedLinePointDefect.
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
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
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
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_MIPStarRE_QPBT_ExtendedLineGame_diagonal_completed_defect_eq_read_defect
import Theorems.Thm_MIPStarRE_QPBT_ExtendedLineGame_diagonal_point_win_iff_read_eq
import Theorems.Thm_MIPStarRE_QPBT_ExtendedLineGame_outcomeWeight_eq_zero_of_invalid
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































private theorem diagonal_rejectedTerm_eq_read_mismatch
    (lines : _root_.MIPStarRE.QPBT.ExtendedLinesWitness setting points deltaL)
    (sample : _root_.MIPStarRE.QPBT.DirectLdSpace P.extendedDirectLd)
    (answerA answerB : _root_.MIPStarRE.QPBT.DirectLdAnswer P.extendedDirectLd) :
    (if _root_.MIPStarRE.QPBT.directLdWinPredicate P.extendedDirectLd
        (.dline, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .dline sample)
        (.point, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .point sample) answerA answerB then
      0
    else _root_.MIPStarRE.QPBT.outcomeWeight (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
      (.dline, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .dline sample)
      (.point, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .point sample) answerA answerB) =
      if _root_.MIPStarRE.QPBT.ExtendedLineGame.diagonalGameRead sample answerA = _root_.MIPStarRE.QPBT.ExtendedLineGame.pointGameRead answerB then 0
      else _root_.MIPStarRE.QPBT.outcomeWeight (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
        (.dline, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .dline sample)
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
  | dlinePolys coeffs =>
      cases answerB with
      | pointVals values =>
          by_cases hwin : _root_.MIPStarRE.QPBT.directLdWinPredicate P.extendedDirectLd
              (.dline, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .dline sample)
              (.point, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .point sample)
              (.dlinePolys coeffs) (.pointVals values) = true
          · have hread := (_root_.MIPStarRE.QPBT.ExtendedLineGame.diagonal_point_win_iff_read_eq sample coeffs values).1 hwin
            simp [hwin, hread]
          · have hread : _root_.MIPStarRE.QPBT.ExtendedLineGame.diagonalGameRead sample (.dlinePolys coeffs) ≠
                _root_.MIPStarRE.QPBT.ExtendedLineGame.pointGameRead (.pointVals values) :=
              fun h => hwin ((_root_.MIPStarRE.QPBT.ExtendedLineGame.diagonal_point_win_iff_read_eq sample coeffs values).2 h)
            simp [hwin, hread]
      | alinePolys coeffsB =>
          rw [_root_.MIPStarRE.QPBT.ExtendedLineGame.outcomeWeight_eq_zero_of_invalid lines _ _ _ _ (Or.inr rfl)]
          simp
      | dlinePolys coeffsB =>
          rw [_root_.MIPStarRE.QPBT.ExtendedLineGame.outcomeWeight_eq_zero_of_invalid lines _ _ _ _ (Or.inr rfl)]
          simp

/-- Fixed-sample diagonal-line/point rejection equals completed-read mismatch mass. -/
theorem diagonal_rejectedMass_eq_read_mismatch
    (lines : _root_.MIPStarRE.QPBT.ExtendedLinesWitness setting points deltaL)
    (sample : _root_.MIPStarRE.QPBT.DirectLdSpace P.extendedDirectLd) :
    _root_.MIPStarRE.QPBT.directRejectedMass P.extendedDirectLd (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
        (.dline, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .dline sample)
        (.point, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .point sample) =
      _root_.MIPStarRE.QPBT.outcomeEventWeight (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
        (.dline, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .dline sample)
        (.point, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .point sample)
        (fun answerA answerB => _root_.MIPStarRE.QPBT.ExtendedLineGame.diagonalGameRead sample answerA ≠ _root_.MIPStarRE.QPBT.ExtendedLineGame.pointGameRead answerB) := by
  classical
  unfold _root_.MIPStarRE.QPBT.directRejectedMass _root_.MIPStarRE.QPBT.outcomeEventWeight
  apply Finset.sum_congr rfl
  intro answerA _
  apply Finset.sum_congr rfl
  intro answerB _
  have hterm := diagonal_rejectedTerm_eq_read_mismatch lines sample answerA answerB
  by_cases hread : _root_.MIPStarRE.QPBT.ExtendedLineGame.diagonalGameRead sample answerA = _root_.MIPStarRE.QPBT.ExtendedLineGame.pointGameRead answerB
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
        (.dline, .point) =
      _root_.MIPStarRE.QPBT.ExtendedLineGame.completedLinePointDefect lines .AA' .BA''
        (_root_.MIPStarRE.QPBT.directDLinePointDist P.extendedDirectLd) := by
  rw [_root_.MIPStarRE.QPBT.directLdBranchRejectionProbability_eq_avgOver]
  calc
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.DirectLdSpace P.extendedDirectLd))
        (fun sample => _root_.MIPStarRE.QPBT.directRejectedMass P.extendedDirectLd (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
          (.dline, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .dline sample)
          (.point, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .point sample)) =
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.DirectLdSpace P.extendedDirectLd))
          (fun sample => _root_.MIPStarRE.QPBT.outcomeEventWeight (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
            (.dline, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .dline sample)
            (.point, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .point sample)
            (fun answerA answerB =>
              _root_.MIPStarRE.QPBT.ExtendedLineGame.diagonalGameRead sample answerA ≠ _root_.MIPStarRE.QPBT.ExtendedLineGame.pointGameRead answerB)) := by
      apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
      exact _root_.MIPStarRE.QPBT.ExtendedLineGame.diagonal_rejectedMass_eq_read_mismatch lines
    _ = _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.DirectLdSpace P.extendedDirectLd))
        (fun sample answer => _root_.MIPStarRE.QPBT.heteroKron
          (((_root_.MIPStarRE.QPBT.ExtendedLineGame.answerMeasurement lines .alice
            (.dline, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .dline sample)).postprocess
              (_root_.MIPStarRE.QPBT.ExtendedLineGame.diagonalGameRead sample)).effect answer) 1)
        (fun sample answer => _root_.MIPStarRE.QPBT.heteroKron 1
          (((_root_.MIPStarRE.QPBT.ExtendedLineGame.answerMeasurement lines .bob
            (.point, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .point sample)).postprocess
              _root_.MIPStarRE.QPBT.ExtendedLineGame.pointGameRead).effect answer))
        (_root_.MIPStarRE.QPBT.ExtendedLineGame.pairState setting) := by
      exact (_root_.MIPStarRE.QPBT.WinImplications.consistencyDefect_postprocess_eq_mismatch
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.DirectLdSpace P.extendedDirectLd)) (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
        (fun sample => (.dline, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .dline sample))
        (fun sample => (.point, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .point sample))
        _root_.MIPStarRE.QPBT.ExtendedLineGame.diagonalGameRead (fun _ => _root_.MIPStarRE.QPBT.ExtendedLineGame.pointGameRead)).symm
    _ = _root_.MIPStarRE.QPBT.ExtendedLineGame.completedLinePointDefect lines .AA' .BA''
        (_root_.MIPStarRE.QPBT.directDLinePointDist P.extendedDirectLd) :=
      (_root_.MIPStarRE.QPBT.ExtendedLineGame.diagonal_completed_defect_eq_read_defect lines).symm
