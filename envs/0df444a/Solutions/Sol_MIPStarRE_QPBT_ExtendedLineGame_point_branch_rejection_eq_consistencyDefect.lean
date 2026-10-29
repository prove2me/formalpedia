-- Prove2me | solution 1 for MIPStarRE.QPBT.ExtendedLineGame.point_branch_rejection_eq_consistencyDefect
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T02:08:28.463984+00:00
-- url     : https://prove2.me/submissions/ff8c1b4c-6f55-4db6-9100-b0f527151503

-- Generated proof for MIPStarRE.QPBT.ExtendedLineGame.point_branch_rejection_eq_consistencyDefect.
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
import Definitions.Def_QPBT_QPBT_Combining_Defs
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Game
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_GameValue
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_BranchComparison
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Combining_GameValue
import Definitions.Def_QPBT_QPBT_Combining_ExtendedLineGame
import Definitions.Def_QPBT_QPBT_Combining_ExtendedLineGame_LinePointRejection
import Definitions.Def_QPBT_QPBT_Combining_Points
import Definitions.Def_QPBT_QPBT_Combining_Witnesses
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_LIDT_MIPStarRE_LDT_avgOver_uniform_equiv_prod
import Theorems.Thm_LIDT_MIPStarRE_Quantum_Measurement_postprocess_comp
import Theorems.Thm_MIPStarRE_QPBT_ExtendedLineGame_outcomeWeight_eq_zero_of_invalid
import Theorems.Thm_MIPStarRE_QPBT_WinImplications_consistencyDefect_postprocess_eq_mismatch
import Theorems.Thm_MIPStarRE_QPBT_consistencyDefect_congr
import Theorems.Thm_MIPStarRE_QPBT_directLdIndexedBranchRejectionProbability_point_point

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.ExtendedLineGame
end MIPStarRE.QPBT.ExtendedLineGame
namespace MIPStarRE.QPBT.ProjectiveSetting
end MIPStarRE.QPBT.ProjectiveSetting

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

/- Source helpers from QPBT/Combining/ExtendedLineGame/PointPointRejection.lean. -/
/-!
# Point/point rejection for the extended direct game

This module bounds the point-agreement branch of the directly indexed
low-degree strategy by the self-consistency error of the supplied joint point
measurements.  The common extended point is transported by one coordinate
equivalence to the jointly uniform tuple `(x, z, alpha, beta)` before the
scalar coarse-graining is applied.

This is a formalization-only auxiliary for the supplied-witness route in the
proof of `lem:qld-4-7`; it does not construct the point witness or establish
the complete passing-value estimate.

## References

- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:689-709`
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1279-1288`
- `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:295-311`
- Issue Dengnifer/MIPStarRE-QPBT-bak#313.
-/

@[expose] public section

open scoped BigOperators MatrixOrder ComplexOrder

set_option synthInstance.maxSize 400

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum
open ProjectiveSetting

noncomputable section

namespace ExtendedLineGame

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {epsilon deltaQ deltaL : ℝ}
variable {setting : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon}
variable {points : _root_.MIPStarRE.QPBT.CombinedPointsWitness setting deltaQ}











private theorem point_point_win_iff_read_eq
    (sample : _root_.MIPStarRE.QPBT.DirectLdSpace P.extendedDirectLd)
    (valuesA valuesB : Fin P.extendedDirectLd.k →
      _root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd) :
    _root_.MIPStarRE.QPBT.directLdWinPredicate P.extendedDirectLd
        (.point, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .point sample)
        (.point, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .point sample)
        (.pointVals valuesA) (.pointVals valuesB) = true ↔
      _root_.MIPStarRE.QPBT.ExtendedLineGame.pointGameRead (.pointVals valuesA) = _root_.MIPStarRE.QPBT.ExtendedLineGame.pointGameRead (.pointVals valuesB) := by
  simp only [_root_.MIPStarRE.QPBT.directLdWinPredicate, _root_.MIPStarRE.QPBT.validDirectLdAnswer,
    Bool.and_self, if_true, decide_eq_true_eq, _root_.MIPStarRE.QPBT.ExtendedLineGame.pointGameRead, Option.some.injEq]
  change valuesA = valuesB ↔
    (_root_.MIPStarRE.QPBT.extendedDirectScalarEquiv P)
        (valuesA ⟨0, by change 0 < 1; decide⟩) =
      (_root_.MIPStarRE.QPBT.extendedDirectScalarEquiv P)
        (valuesB ⟨0, by change 0 < 1; decide⟩)
  constructor
  · intro h
    rw [h]
  · intro h
    funext i
    have hval : i.val = 0 := by
      have hlt : i.val < 1 := i.isLt
      omega
    have hi : i = ⟨0, by change 0 < 1; decide⟩ := Fin.ext hval
    subst i
    exact (_root_.MIPStarRE.QPBT.extendedDirectScalarEquiv P).injective h

private theorem point_rejected_term_eq_read_mismatch
    (lines : _root_.MIPStarRE.QPBT.ExtendedLinesWitness setting points deltaL)
    (sample : _root_.MIPStarRE.QPBT.DirectLdSpace P.extendedDirectLd)
    (answerA answerB : _root_.MIPStarRE.QPBT.DirectLdAnswer P.extendedDirectLd) :
    (if _root_.MIPStarRE.QPBT.directLdWinPredicate P.extendedDirectLd
        (.point, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .point sample)
        (.point, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .point sample) answerA answerB then
      0
    else _root_.MIPStarRE.QPBT.outcomeWeight (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
      (.point, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .point sample)
      (.point, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .point sample) answerA answerB) =
      if _root_.MIPStarRE.QPBT.ExtendedLineGame.pointGameRead answerA = _root_.MIPStarRE.QPBT.ExtendedLineGame.pointGameRead answerB then 0
      else _root_.MIPStarRE.QPBT.outcomeWeight (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
        (.point, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .point sample)
        (.point, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .point sample) answerA answerB := by
  classical
  cases answerA with
  | pointVals valuesA =>
      cases answerB with
      | pointVals valuesB =>
          have hiff := point_point_win_iff_read_eq (P := P) sample valuesA valuesB
          exact if_congr hiff rfl rfl
      | alinePolys _ =>
          rw [_root_.MIPStarRE.QPBT.ExtendedLineGame.outcomeWeight_eq_zero_of_invalid lines _ _ _ _ (Or.inr rfl)]
          simp [_root_.MIPStarRE.QPBT.ExtendedLineGame.pointGameRead, _root_.MIPStarRE.QPBT.directLdWinPredicate, _root_.MIPStarRE.QPBT.validDirectLdAnswer]
      | dlinePolys _ =>
          rw [_root_.MIPStarRE.QPBT.ExtendedLineGame.outcomeWeight_eq_zero_of_invalid lines _ _ _ _ (Or.inr rfl)]
          simp [_root_.MIPStarRE.QPBT.ExtendedLineGame.pointGameRead, _root_.MIPStarRE.QPBT.directLdWinPredicate, _root_.MIPStarRE.QPBT.validDirectLdAnswer]
  | alinePolys _ =>
      rw [_root_.MIPStarRE.QPBT.ExtendedLineGame.outcomeWeight_eq_zero_of_invalid lines _ _ _ _ (Or.inl rfl)]
      cases answerB <;> simp [_root_.MIPStarRE.QPBT.ExtendedLineGame.pointGameRead, _root_.MIPStarRE.QPBT.directLdWinPredicate, _root_.MIPStarRE.QPBT.validDirectLdAnswer]
  | dlinePolys _ =>
      rw [_root_.MIPStarRE.QPBT.ExtendedLineGame.outcomeWeight_eq_zero_of_invalid lines _ _ _ _ (Or.inl rfl)]
      cases answerB <;> simp [_root_.MIPStarRE.QPBT.ExtendedLineGame.pointGameRead, _root_.MIPStarRE.QPBT.directLdWinPredicate, _root_.MIPStarRE.QPBT.validDirectLdAnswer]

private theorem point_rejectedMass_eq_read_mismatch
    (lines : _root_.MIPStarRE.QPBT.ExtendedLinesWitness setting points deltaL)
    (sample : _root_.MIPStarRE.QPBT.DirectLdSpace P.extendedDirectLd) :
    _root_.MIPStarRE.QPBT.directRejectedMass P.extendedDirectLd (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
        (.point, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .point sample)
        (.point, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .point sample) =
      _root_.MIPStarRE.QPBT.outcomeEventWeight (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
        (.point, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .point sample)
        (.point, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .point sample)
        (fun answerA answerB => _root_.MIPStarRE.QPBT.ExtendedLineGame.pointGameRead answerA ≠ _root_.MIPStarRE.QPBT.ExtendedLineGame.pointGameRead answerB) := by
  classical
  unfold _root_.MIPStarRE.QPBT.directRejectedMass _root_.MIPStarRE.QPBT.outcomeEventWeight
  apply Finset.sum_congr rfl
  intro answerA _
  apply Finset.sum_congr rfl
  intro answerB _
  have hterm := point_rejected_term_eq_read_mismatch lines sample answerA answerB
  by_cases hread : _root_.MIPStarRE.QPBT.ExtendedLineGame.pointGameRead answerA = _root_.MIPStarRE.QPBT.ExtendedLineGame.pointGameRead answerB
  · simpa [hread] using hterm
  · simpa [hread] using hterm

/-- The completed point read of the direct-game answer measurement is the
corresponding scalar coarse-graining of the supplied joint point measurement. -/
theorem point_read_effect
    (lines : _root_.MIPStarRE.QPBT.ExtendedLinesWitness setting points deltaL) (side : _root_.MIPStarRE.QPBT.PlayerSide)
    (sample : _root_.MIPStarRE.QPBT.DirectLdSpace P.extendedDirectLd) (answer : Option (_root_.MIPStarRE.QPBT.PauliScalar P)) :
    (((_root_.MIPStarRE.QPBT.ExtendedLineGame.answerMeasurement lines side
        (.point, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .point sample)).postprocess
      _root_.MIPStarRE.QPBT.ExtendedLineGame.pointGameRead).effect answer) =
      ((points.Q side
        (_root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P sample.point))
        (_root_.MIPStarRE.QPBT.projZ (_root_.MIPStarRE.QPBT.directPointToPauli P sample.point))).postprocess fun values =>
          some (_root_.MIPStarRE.QPBT.directPointToPauli P sample.point (_root_.MIPStarRE.QPBT.alphaVar P.m) * values.1 +
            _root_.MIPStarRE.QPBT.directPointToPauli P sample.point (_root_.MIPStarRE.QPBT.betaVar P.m) * values.2)).effect answer := by
  classical
  unfold _root_.MIPStarRE.QPBT.ExtendedLineGame.answerMeasurement _root_.MIPStarRE.QPBT.CombinedPointsWitness.extendedQ
  rw [_root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_comp,
    _root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_comp]
  rfl





end ExtendedLineGame

end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/DirectLowDegree/Transport/Combining/GameValue.lean. -/
/-!
# Index-conditioned rejection probabilities of the directly indexed game

`lem:ld-combined-value` transports the value of a strategy along
`def:ld-combined-strategy` by splitting each branch of the combined game
according to the event of `lem:ld-combined-question-law`, that is according to
whether the stored coordinate index of the common sample is a point coordinate
or a combining coordinate.  This module provides the corresponding refinement
of the branch rejection probability: the uniform average over the common sample
is the uniform average over the stored coordinate index of the average over the
sampled point and the sampled direction alone.

The point-versus-point branch is recorded separately, because it is the branch
that the combining coordinates of the combined game reduce to: both of its
questions are the point question at the sampled point, so its rejected mass
depends on neither the stored coordinate index nor the sampled direction.

All declarations below are formalization-only support derived from the game
value; none is a paper-labelled result.

## References

* `references/neexp-paper/05_quantum_preliminaries.tex:1409-1503`
* `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`
* `blueprint/src/chapter/ch13_qpbt_test.tex:517-568`
-/

@[expose] public section

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.LDT.Preliminaries
open LIDT.MIPStarRE.Quantum

noncomputable section

/-! ## The index-conditioned branch rejection probability -/





/-- The branch rejection probability of an ordered type pair is the uniform
average over the stored coordinate index of the index-conditioned rejection
probabilities.  This is the refinement used to split a branch of the combined
game according to the event of `lem:ld-combined-question-law`, whose two cases
are the point coordinates and the combining coordinates of the combined
dimension. -/
theorem directLdBranchRejectionProbability_eq_avgOver_index
    (D : _root_.MIPStarRE.QPBT.DirectLdParams) (S : _root_.MIPStarRE.QPBT.Strategy (_root_.MIPStarRE.QPBT.directLdGame D))
    (types : _root_.MIPStarRE.QPBT.LdType × _root_.MIPStarRE.QPBT.LdType) :
    _root_.MIPStarRE.QPBT.directLdBranchRejectionProbability D S types =
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin D.m))
        (_root_.MIPStarRE.QPBT.directLdIndexedBranchRejectionProbability D S types) := by
  rw [_root_.MIPStarRE.QPBT.directLdBranchRejectionProbability_eq_avgOver]
  exact _root_.LIDT.MIPStarRE.LDT.avgOver_uniform_equiv_prod (e := _root_.MIPStarRE.QPBT.directLdSpaceIndexEquiv D) _

/-! ## The point-versus-point branch -/



/-- The point-versus-point branch rejection probability is the uniform average
over the sampled point of the rejected mass at the two equal point questions.
This is the branch to which the combining coordinates of the combined game
reduce, by `directCombined_measuredQuestion_of_coefficientVar`. -/
theorem directLdBranchRejectionProbability_point_point_eq
    (D : _root_.MIPStarRE.QPBT.DirectLdParams) (S : _root_.MIPStarRE.QPBT.Strategy (_root_.MIPStarRE.QPBT.directLdGame D)) :
    _root_.MIPStarRE.QPBT.directLdBranchRejectionProbability D S (.point, .point) =
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D)) fun u =>
        _root_.MIPStarRE.QPBT.directRejectedMass D S (_root_.MIPStarRE.QPBT.directLdPointQuestionOf D u)
          (_root_.MIPStarRE.QPBT.directLdPointQuestionOf D u) := by
  rw [_root_.MIPStarRE.QPBT.directLdBranchRejectionProbability_eq_avgOver_index,
    show _root_.MIPStarRE.QPBT.directLdIndexedBranchRejectionProbability D S (.point, .point) =
      fun _ => _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D)) fun u =>
        _root_.MIPStarRE.QPBT.directRejectedMass D S (_root_.MIPStarRE.QPBT.directLdPointQuestionOf D u)
          (_root_.MIPStarRE.QPBT.directLdPointQuestionOf D u) from
      funext (_root_.MIPStarRE.QPBT.directLdIndexedBranchRejectionProbability_point_point D S)]
  exact _root_.LIDT.MIPStarRE.LDT.avgOver_uniform_const _

/-! ## The rejected mass of the combined strategy -/





end

end MIPStarRE.QPBT

/-!
# Point/point rejection for the extended direct game

This module bounds the point-agreement branch of the directly indexed
low-degree strategy by the self-consistency error of the supplied joint point
measurements.  The common extended point is transported by one coordinate
equivalence to the jointly uniform tuple `(x, z, alpha, beta)` before the
scalar coarse-graining is applied.

This is a formalization-only auxiliary for the supplied-witness route in the
proof of `lem:qld-4-7`; it does not construct the point witness or establish
the complete passing-value estimate.

## References

- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:689-709`
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1279-1288`
- `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:295-311`
- Issue Dengnifer/MIPStarRE-QPBT-bak#313.
-/



open scoped BigOperators MatrixOrder ComplexOrder

set_option synthInstance.maxSize 400

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum
open MIPStarRE.QPBT.ProjectiveSetting



open MIPStarRE.QPBT.ExtendedLineGame

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {epsilon deltaQ deltaL : ℝ}
variable {setting : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon}
variable {points : _root_.MIPStarRE.QPBT.CombinedPointsWitness setting deltaQ}

theorem solution
    (lines : _root_.MIPStarRE.QPBT.ExtendedLinesWitness setting points deltaL) :
    _root_.MIPStarRE.QPBT.directLdBranchRejectionProbability P.extendedDirectLd (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
        (.point, .point) =
      _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution
        (Fin P.extendedDirectLd.m → _root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd))
        (fun u answer => _root_.MIPStarRE.QPBT.heteroKron
          (((points.Q .alice
            (_root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P u))
            (_root_.MIPStarRE.QPBT.projZ (_root_.MIPStarRE.QPBT.directPointToPauli P u))).postprocess fun values =>
              some (_root_.MIPStarRE.QPBT.directPointToPauli P u (_root_.MIPStarRE.QPBT.alphaVar P.m) * values.1 +
                _root_.MIPStarRE.QPBT.directPointToPauli P u (_root_.MIPStarRE.QPBT.betaVar P.m) * values.2)).effect answer) 1)
        (fun u answer => _root_.MIPStarRE.QPBT.heteroKron 1
          (((points.Q .bob
            (_root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P u))
            (_root_.MIPStarRE.QPBT.projZ (_root_.MIPStarRE.QPBT.directPointToPauli P u))).postprocess fun values =>
              some (_root_.MIPStarRE.QPBT.directPointToPauli P u (_root_.MIPStarRE.QPBT.alphaVar P.m) * values.1 +
                _root_.MIPStarRE.QPBT.directPointToPauli P u (_root_.MIPStarRE.QPBT.betaVar P.m) * values.2)).effect answer))
        (_root_.MIPStarRE.QPBT.ExtendedLineGame.pairState setting) := by
  rw [_root_.MIPStarRE.QPBT.directLdBranchRejectionProbability_point_point_eq]
  calc
    _ = _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution
          (Fin P.extendedDirectLd.m → _root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd))
        (fun u => _root_.MIPStarRE.QPBT.outcomeEventWeight (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
          (_root_.MIPStarRE.QPBT.directLdPointQuestionOf P.extendedDirectLd u)
          (_root_.MIPStarRE.QPBT.directLdPointQuestionOf P.extendedDirectLd u)
          (fun answerA answerB => _root_.MIPStarRE.QPBT.ExtendedLineGame.pointGameRead answerA ≠ _root_.MIPStarRE.QPBT.ExtendedLineGame.pointGameRead answerB)) := by
      apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
      intro u
      simpa [_root_.MIPStarRE.QPBT.directLdPointQuestionOf, _root_.MIPStarRE.QPBT.directLdMap] using
        point_rejectedMass_eq_read_mismatch lines
          ⟨u, P.extendedDirectLd.firstIndex, 0⟩
    _ = _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution
          (Fin P.extendedDirectLd.m → _root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd))
        (fun u answer => _root_.MIPStarRE.QPBT.heteroKron
          ((((_root_.MIPStarRE.QPBT.ExtendedLineGame.answerMeasurement lines .alice
            (_root_.MIPStarRE.QPBT.directLdPointQuestionOf P.extendedDirectLd u)).postprocess
              _root_.MIPStarRE.QPBT.ExtendedLineGame.pointGameRead).effect answer)) 1)
        (fun u answer => _root_.MIPStarRE.QPBT.heteroKron 1
          ((((_root_.MIPStarRE.QPBT.ExtendedLineGame.answerMeasurement lines .bob
            (_root_.MIPStarRE.QPBT.directLdPointQuestionOf P.extendedDirectLd u)).postprocess
              _root_.MIPStarRE.QPBT.ExtendedLineGame.pointGameRead).effect answer)))
        (_root_.MIPStarRE.QPBT.ExtendedLineGame.pairState setting) :=
      (_root_.MIPStarRE.QPBT.WinImplications.consistencyDefect_postprocess_eq_mismatch
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution
          (Fin P.extendedDirectLd.m → _root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd))
        (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
        (fun u => _root_.MIPStarRE.QPBT.directLdPointQuestionOf P.extendedDirectLd u)
        (fun u => _root_.MIPStarRE.QPBT.directLdPointQuestionOf P.extendedDirectLd u)
        (fun _ => _root_.MIPStarRE.QPBT.ExtendedLineGame.pointGameRead) (fun _ => _root_.MIPStarRE.QPBT.ExtendedLineGame.pointGameRead)).symm
    _ = _ := by
      apply _root_.MIPStarRE.QPBT.consistencyDefect_congr <;> intro u answer
      · rw [show _root_.MIPStarRE.QPBT.directLdPointQuestionOf P.extendedDirectLd u =
            (.point, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .point
              ⟨u, P.extendedDirectLd.firstIndex, 0⟩) by rfl,
          _root_.MIPStarRE.QPBT.ExtendedLineGame.point_read_effect lines .alice]
      · rw [show _root_.MIPStarRE.QPBT.directLdPointQuestionOf P.extendedDirectLd u =
            (.point, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .point
              ⟨u, P.extendedDirectLd.firstIndex, 0⟩) by rfl,
          _root_.MIPStarRE.QPBT.ExtendedLineGame.point_read_effect lines .bob]
