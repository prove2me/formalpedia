-- Prove2me | solution 1 for MIPStarRE.QPBT.directCoordinate_failure_le_weightedFailure
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T22:40:57.17019+00:00
-- url     : https://prove2.me/submissions/cc8a16db-581d-46a5-9b8d-37a38d4c2d27

-- Generated proof for MIPStarRE.QPBT.directCoordinate_failure_le_weightedFailure.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Families
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Interpolation
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_AvgCongr
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyBiProj_Measurements
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_Lines
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Game
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_GameValue
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_BranchComparison
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Correspondence
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Questions
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Strategy
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_StrategyClasses
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Mathlib
import Theorems.Thm_LIDT_MIPStarRE_LDT_ProjStrat_lowIndividualDegreeFailureProbability_eq_role_averages
import Theorems.Thm_MIPStarRE_QPBT_directAxisAnswerReadout_zeroCoord_eq_of_win
import Theorems.Thm_MIPStarRE_QPBT_directCoordinate_diagonal_line_point_le
import Theorems.Thm_MIPStarRE_QPBT_directCoordinate_diagonal_point_line_le
import Theorems.Thm_MIPStarRE_QPBT_directCoordinate_point_agreement_le
import Theorems.Thm_MIPStarRE_QPBT_directPointAnswerReadout_eq_axis_zeroCoord_of_win
import Theorems.Thm_MIPStarRE_QPBT_qBipartiteConsDefect_le_directRejectedMass

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/DirectLowDegree/Geometry.lean. -/
/-!
# Geometry for the directly indexed low-degree game

This module defines the parameters, line carrier, and line-point distributions
for the directly indexed low-degree game.

## References

The line-point distributions originate in
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:243-272`.
The directly indexed repair is documented in
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.LDT.Preliminaries
open LIDT.MIPStarRE.Quantum

noncomputable section









instance instNonemptyFinM_1 (D : _root_.MIPStarRE.QPBT.DirectLdParams) : Nonempty (Fin D.m) := ⟨D.firstIndex⟩



















/-! ## Finite direct-line carrier -/

















































end

end MIPStarRE.QPBT

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

/-- Admissible field sizes are positive, so LDT points over a direct
parameter tuple form a nonempty type. -/
instance instNeZeroNatQ (D : _root_.MIPStarRE.QPBT.DirectLdParams) : NeZero D.q :=
  ⟨Nat.ne_of_gt D.toLDTParameters.hq⟩

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

section PointAxisBranches

variable (D : _root_.MIPStarRE.QPBT.DirectLdParams) (S : _root_.MIPStarRE.QPBT.Strategy (_root_.MIPStarRE.QPBT.directLdGame D))
  (hS : S.IsProjective) (r : Fin D.k)





/-- Axis-line defect with the line on the left is at most the rejected direct
mass at the canonical direct questions of the reindexed sample. -/
private theorem axis_line_point_defect_le
    (s : _root_.LIDT.MIPStarRE.LDT.AxisParallelTestSample D.toLDTParameters) :
    letI := D.toLDTFieldModel
    _root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect (_root_.MIPStarRE.QPBT.directCoordinateProjStrat D S hS r).state
        ((_root_.MIPStarRE.QPBT.directCoordinateProjStrat D S hS r).axisParallelLineAnswerFamilyA s)
        ((_root_.MIPStarRE.QPBT.directCoordinateProjStrat D S hS r).axisParallelPointAnswerFamilyB s) ≤
      _root_.MIPStarRE.QPBT.directRejectedMass D S
        (.aline, ⟨_root_.MIPStarRE.QPBT.lineRepMap (_root_.MIPStarRE.QPBT.coordinateDirection (Fin.rev s.2))
          (_root_.MIPStarRE.QPBT.ldtPointToDirect D s.1), Fin.rev s.2, 0⟩)
        (_root_.MIPStarRE.QPBT.directLdPointQuestionOf D (_root_.MIPStarRE.QPBT.ldtPointToDirect D s.1)) := by
  letI := D.toLDTFieldModel
  have h := _root_.MIPStarRE.QPBT.qBipartiteConsDefect_le_directRejectedMass D S hS
    (_root_.MIPStarRE.QPBT.directAxisQuestionOf D ⟨s.1, s.2⟩) (_root_.MIPStarRE.QPBT.directPointQuestionOf D s.1)
    (fun a => _root_.MIPStarRE.QPBT.directAxisAnswerReadout D r ⟨s.1, s.2⟩ a _root_.LIDT.MIPStarRE.LDT.zeroCoord)
    (_root_.MIPStarRE.QPBT.directPointAnswerReadout D r)
    (fun a b hab =>
      _root_.MIPStarRE.QPBT.directAxisAnswerReadout_zeroCoord_eq_of_win D r ⟨s.1, s.2⟩ a b hab)
  change _root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect (_root_.MIPStarRE.QPBT.strategyQuantumState S)
      (_root_.LIDT.MIPStarRE.LDT.postprocess
        (_root_.LIDT.MIPStarRE.LDT.ProjMeas.postprocess
          (_root_.MIPStarRE.QPBT.matrixMeasurementToLDTProjMeas
            (S.A (_root_.MIPStarRE.QPBT.directAxisQuestionOf D ⟨s.1, s.2⟩))
            (hS.1 (_root_.MIPStarRE.QPBT.directAxisQuestionOf D ⟨s.1, s.2⟩)))
          (_root_.MIPStarRE.QPBT.directAxisAnswerReadout D r ⟨s.1, s.2⟩)).toSubMeas
        (fun g => g _root_.LIDT.MIPStarRE.LDT.zeroCoord))
      (_root_.LIDT.MIPStarRE.LDT.ProjMeas.postprocess
        (_root_.MIPStarRE.QPBT.matrixMeasurementToLDTProjMeas
          (S.B (_root_.MIPStarRE.QPBT.directPointQuestionOf D s.1))
          (hS.2 (_root_.MIPStarRE.QPBT.directPointQuestionOf D s.1)))
        (_root_.MIPStarRE.QPBT.directPointAnswerReadout D r)).toSubMeas ≤ _
  simp only [ProjMeas.postprocess_toSubMeas, _root_.LIDT.MIPStarRE.LDT.SubMeas.postprocess_comp] at h ⊢
  exact h

/-- Axis-line defect with the point on the left is at most the rejected direct
mass at the canonical direct questions of the reindexed sample. -/
private theorem axis_point_line_defect_le
    (s : _root_.LIDT.MIPStarRE.LDT.AxisParallelTestSample D.toLDTParameters) :
    letI := D.toLDTFieldModel
    _root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect (_root_.MIPStarRE.QPBT.directCoordinateProjStrat D S hS r).state
        ((_root_.MIPStarRE.QPBT.directCoordinateProjStrat D S hS r).axisParallelPointAnswerFamilyA s)
        ((_root_.MIPStarRE.QPBT.directCoordinateProjStrat D S hS r).axisParallelLineAnswerFamilyB s) ≤
      _root_.MIPStarRE.QPBT.directRejectedMass D S
        (_root_.MIPStarRE.QPBT.directLdPointQuestionOf D (_root_.MIPStarRE.QPBT.ldtPointToDirect D s.1))
        (.aline, ⟨_root_.MIPStarRE.QPBT.lineRepMap (_root_.MIPStarRE.QPBT.coordinateDirection (Fin.rev s.2))
          (_root_.MIPStarRE.QPBT.ldtPointToDirect D s.1), Fin.rev s.2, 0⟩) := by
  letI := D.toLDTFieldModel
  have h := _root_.MIPStarRE.QPBT.qBipartiteConsDefect_le_directRejectedMass D S hS
    (_root_.MIPStarRE.QPBT.directPointQuestionOf D s.1) (_root_.MIPStarRE.QPBT.directAxisQuestionOf D ⟨s.1, s.2⟩)
    (_root_.MIPStarRE.QPBT.directPointAnswerReadout D r)
    (fun b => _root_.MIPStarRE.QPBT.directAxisAnswerReadout D r ⟨s.1, s.2⟩ b _root_.LIDT.MIPStarRE.LDT.zeroCoord)
    (fun a b hab =>
      _root_.MIPStarRE.QPBT.directPointAnswerReadout_eq_axis_zeroCoord_of_win D r ⟨s.1, s.2⟩ a b hab)
  change _root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect (_root_.MIPStarRE.QPBT.strategyQuantumState S)
      (_root_.LIDT.MIPStarRE.LDT.ProjMeas.postprocess
        (_root_.MIPStarRE.QPBT.matrixMeasurementToLDTProjMeas
          (S.A (_root_.MIPStarRE.QPBT.directPointQuestionOf D s.1))
          (hS.1 (_root_.MIPStarRE.QPBT.directPointQuestionOf D s.1)))
        (_root_.MIPStarRE.QPBT.directPointAnswerReadout D r)).toSubMeas
      (_root_.LIDT.MIPStarRE.LDT.postprocess
        (_root_.LIDT.MIPStarRE.LDT.ProjMeas.postprocess
          (_root_.MIPStarRE.QPBT.matrixMeasurementToLDTProjMeas
            (S.B (_root_.MIPStarRE.QPBT.directAxisQuestionOf D ⟨s.1, s.2⟩))
            (hS.2 (_root_.MIPStarRE.QPBT.directAxisQuestionOf D ⟨s.1, s.2⟩)))
          (_root_.MIPStarRE.QPBT.directAxisAnswerReadout D r ⟨s.1, s.2⟩)).toSubMeas
        (fun g => g _root_.LIDT.MIPStarRE.LDT.zeroCoord)) ≤ _
  simp only [ProjMeas.postprocess_toSubMeas, _root_.LIDT.MIPStarRE.LDT.SubMeas.postprocess_comp] at h ⊢
  exact h

/-- Reindex a uniform average over LDT axis samples to the direct sample
space; the averaged function depends only on the decoded point and the
reversed coordinate index. -/
private theorem avgOver_axis_sample_eq
    (f : (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D) × Fin D.m → ℝ) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.AxisParallelTestSample D.toLDTParameters))
        (fun s => f (_root_.MIPStarRE.QPBT.ldtPointToDirect D s.1, Fin.rev s.2)) =
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.DirectLdSpace D))
        (fun sample => f (sample.point, sample.index)) := by
  calc
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.AxisParallelTestSample D.toLDTParameters))
        (fun s => f (_root_.MIPStarRE.QPBT.ldtPointToDirect D s.1, Fin.rev s.2)) =
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution ((Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D) × Fin D.m)) f := by
      rw [_root_.LIDT.MIPStarRE.LDT.avgOver_uniform_equiv ((_root_.MIPStarRE.QPBT.directPointEquiv D).prodCongr Fin.revPerm) f]
      apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
      intro s
      rfl
    _ = _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.DirectLdSpace D))
        (fun sample => f (_root_.MIPStarRE.QPBT.directLdSpaceSplitEquiv D sample).1) :=
      (_root_.LIDT.MIPStarRE.LDT.avgOver_uniform_equiv_fst (_root_.MIPStarRE.QPBT.directLdSpaceSplitEquiv D) f).symm
    _ = _ := by
      apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
      intro sample
      rfl

/-- The axis-line failure with the line on the left is at most the
axis-line/point branch rejection of the direct game. -/
theorem directCoordinate_axis_line_point_le :
    letI := D.toLDTFieldModel
    (_root_.MIPStarRE.QPBT.directCoordinateProjStrat D S hS r).axisParallelLineLeftPointRightFailureProbability ≤
      _root_.MIPStarRE.QPBT.directLdBranchRejectionProbability D S (.aline, .point) := by
  letI := D.toLDTFieldModel
  unfold _root_.LIDT.MIPStarRE.LDT.ProjStrat.axisParallelLineLeftPointRightFailureProbability _root_.LIDT.MIPStarRE.LDT.bipartiteConsError
  refine le_trans
    (_root_.LIDT.MIPStarRE.LDT.avgOver_mono _ _ _ fun s => axis_line_point_defect_le D S hS r s) (le_of_eq ?_)
  rw [_root_.MIPStarRE.QPBT.directLdBranchRejectionProbability_eq_avgOver]
  exact avgOver_axis_sample_eq D (fun pi =>
    _root_.MIPStarRE.QPBT.directRejectedMass D S
      (.aline, ⟨_root_.MIPStarRE.QPBT.lineRepMap (_root_.MIPStarRE.QPBT.coordinateDirection pi.2) pi.1, pi.2, 0⟩)
      (_root_.MIPStarRE.QPBT.directLdPointQuestionOf D pi.1))

/-- The axis-line failure with the point on the left is at most the
point/axis-line branch rejection of the direct game. -/
theorem directCoordinate_axis_point_line_le :
    letI := D.toLDTFieldModel
    (_root_.MIPStarRE.QPBT.directCoordinateProjStrat D S hS r).axisParallelPointLeftLineRightFailureProbability ≤
      _root_.MIPStarRE.QPBT.directLdBranchRejectionProbability D S (.point, .aline) := by
  letI := D.toLDTFieldModel
  unfold _root_.LIDT.MIPStarRE.LDT.ProjStrat.axisParallelPointLeftLineRightFailureProbability _root_.LIDT.MIPStarRE.LDT.bipartiteConsError
  refine le_trans
    (_root_.LIDT.MIPStarRE.LDT.avgOver_mono _ _ _ fun s => axis_point_line_defect_le D S hS r s) (le_of_eq ?_)
  rw [_root_.MIPStarRE.QPBT.directLdBranchRejectionProbability_eq_avgOver]
  exact avgOver_axis_sample_eq D (fun pi =>
    _root_.MIPStarRE.QPBT.directRejectedMass D S
      (_root_.MIPStarRE.QPBT.directLdPointQuestionOf D pi.1)
      (.aline, ⟨_root_.MIPStarRE.QPBT.lineRepMap (_root_.MIPStarRE.QPBT.coordinateDirection pi.2) pi.1, pi.2, 0⟩))

end PointAxisBranches

end

end MIPStarRE.QPBT

/-!
# Pass conversion for the directly indexed low-degree game

This module converts a value bound for a projective strategy of the directly
indexed low-degree game into the hypothesis of the low individual degree
theorem for each coordinate strategy `directCoordinateProjStrat`.

The LDT failure probability gives weight `1/3` to point agreement and
`1/6` to each of the four oriented line-versus-point checks.  The branch
comparisons of `Transport.BranchComparison` and `Transport.DiagonalRecursion`
bound the point and axis-line branches by the corresponding direct branch
rejections and each diagonal branch by twice its direct branch rejection.  The
factor-three rejection calculus of `GameValue` gives the line branches half the
weight of the point branch, so the factor two is absorbed: a direct strategy of
value at least `1 - ε` has coordinate strategies of LDT failure at most
`3 * ε`, which is exactly `PassesLowIndividualDegreeTest (3 * ε)`.

## References

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:214-458`
- `references/ldt-paper/test_definition.tex:130-151`
- Blueprint `def:ld-question-distribution`, `lem:ld-aline-level`,
  `lem:ld-dline-level`, `lem:ld-question-typed-cl`, `lem:alnf`, `lem:dlnf`,
  `def:ld-win-predicate`, `rem:ld-win-zero-direction`, and `def:ld-meas`
- `MIPStarRE/LDT/Test/StrategyFailures.lean:18-130`
- `MIPStarRE/LDT/Test/MainTheorem/MainFormal.lean:300-311`
- `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`
-/



open scoped BigOperators MatrixOrder Matrix ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.Quantum



/-! ## The failure comparison and the pass hypothesis -/

theorem solution
    (D : _root_.MIPStarRE.QPBT.DirectLdParams) (S : _root_.MIPStarRE.QPBT.Strategy (_root_.MIPStarRE.QPBT.directLdGame D))
    (hS : S.IsProjective) (r : Fin D.k) :
    letI := D.toLDTFieldModel
    (_root_.MIPStarRE.QPBT.directCoordinateProjStrat D S hS r).lowIndividualDegreeFailureProbability ≤
      _root_.MIPStarRE.QPBT.directLdLdtWeightedFailureProbability D S +
        (_root_.MIPStarRE.QPBT.directLdBranchRejectionProbability D S (.dline, .point) +
          _root_.MIPStarRE.QPBT.directLdBranchRejectionProbability D S (.point, .dline)) / 6 := by
  letI := D.toLDTFieldModel
  rw [_root_.LIDT.MIPStarRE.LDT.ProjStrat.lowIndividualDegreeFailureProbability_eq_role_averages]
  unfold _root_.LIDT.MIPStarRE.LDT.ProjStrat.axisParallelRoleAverage _root_.LIDT.MIPStarRE.LDT.ProjStrat.diagonalRoleAverage
    _root_.MIPStarRE.QPBT.directLdLdtWeightedFailureProbability
  dsimp only
  have h1 := _root_.MIPStarRE.QPBT.directCoordinate_axis_line_point_le D S hS r
  have h2 := _root_.MIPStarRE.QPBT.directCoordinate_axis_point_line_le D S hS r
  have h3 := _root_.MIPStarRE.QPBT.directCoordinate_point_agreement_le D S hS r
  have h4 := _root_.MIPStarRE.QPBT.directCoordinate_diagonal_line_point_le D S hS r
  have h5 := _root_.MIPStarRE.QPBT.directCoordinate_diagonal_point_line_le D S hS r
  linarith
