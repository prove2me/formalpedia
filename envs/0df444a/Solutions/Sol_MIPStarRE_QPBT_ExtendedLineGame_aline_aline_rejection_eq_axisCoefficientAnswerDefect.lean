-- Prove2me | solution 1 for MIPStarRE.QPBT.ExtendedLineGame.aline_aline_rejection_eq_axisCoefficientAnswerDefect
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T21:42:28.800691+00:00
-- url     : https://prove2.me/submissions/db25187e-5aa5-42d8-80af-15f4f3fd81ac

-- Generated proof for MIPStarRE.QPBT.ExtendedLineGame.aline_aline_rejection_eq_axisCoefficientAnswerDefect.
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
import Definitions.Def_QPBT_QPBT_Algebra_Lines
import Definitions.Def_QPBT_QPBT_Algebra_LowDegreeCode
import Definitions.Def_QPBT_QPBT_Combining_Defs
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Game
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_GameValue
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_BranchComparison
import Definitions.Def_QPBT_QPBT_Combining_ExtendedLineGame
import Definitions.Def_QPBT_QPBT_Combining_ExtendedLineGame_SameLineRejection
import Definitions.Def_QPBT_QPBT_Combining_Points
import Definitions.Def_QPBT_QPBT_Combining_Witnesses
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Games_DistributionAux
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_Observables_LineDefs
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_MIPStarRE_QPBT_ExtendedLineGame_outcomeWeight_eq_zero_of_invalid

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
end LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus
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





















/-- Re-reading a canonical axis question preserves its line description. -/
theorem axis_description_canonical (params : _root_.MIPStarRE.QPBT.DirectLdParams) (sample : _root_.MIPStarRE.QPBT.DirectLdSpace params) :
    _root_.MIPStarRE.QPBT.directALineDescOf params (_root_.MIPStarRE.QPBT.directLdMap params .aline sample) =
      _root_.MIPStarRE.QPBT.directALineDescOf params sample := by
  simp [_root_.MIPStarRE.QPBT.directALineDescOf, _root_.MIPStarRE.QPBT.directLdMap, _root_.MIPStarRE.QPBT.lineRepMap_apply_self]







variable {params : _root_.MIPStarRE.QPBT.AdmissibleParams} {epsilon deltaQ deltaL : ℝ}
variable {setting : _root_.MIPStarRE.QPBT.ProjectiveSetting params epsilon}
variable {points : _root_.MIPStarRE.QPBT.CombinedPointsWitness setting deltaQ}



































end ExtendedLineGame

end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Games/DistanceTheorems/Support.lean. -/
/-!
# Finite-dimensional operator estimates for state-dependent distance

This module contains finite-dimensional operator and finite-sum identities used
by the paper-facing distance theorems. It introduces no new mathematical
assumptions or source-facing statements.

## References

- `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:295-395`
- `references/ldt-paper/preliminaries.tex:649-666`
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.DistanceCalculus

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum
open LIDT.MIPStarRE.LDT.MakingMeasurementsProjective























































/-- Formalization-only auxiliary lemma for the agreement facts (Facts 4.13 and
4.14): the matrix-vector term in `consistencyDefect` is the state quadratic
form. -/
theorem consistency_term_eq_stateQForm {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) (M : _root_.LIDT.MIPStarRE.Quantum.Op ι) :
    (inner ℂ ψ ((EuclideanSpace.equiv ι ℂ).symm (M.mulVec ψ))).re =
      _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ M := by
  rfl



































end MIPStarRE.QPBT.DistanceCalculus

/- Source helpers from QPBT/Games/DistanceTheorems/TensorSupport.lean. -/
/-!
# Tensor-placement and marginal identities

This module collects tensor-placement, marginal, and finite-fiber identities
used in data processing and the commutator estimate.

## References

- `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:397-461`
- Blueprint `fact:triangle-for-simeq`, `fact:data-processing`, and
  `lem:commutation-analysis`
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.DistanceCalculus

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum
open LIDT.MIPStarRE.LDT.MakingMeasurementsProjective





/-- Formalization-only auxiliary lemma for Fact 4.26: products of left and right
placements evaluate as a Kronecker product. -/
theorem placed_product_stateQForm_eq {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (A : _root_.LIDT.MIPStarRE.Quantum.Op ιA) (B : _root_.LIDT.MIPStarRE.Quantum.Op ιB) :
    _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron A 1 * _root_.MIPStarRE.QPBT.heteroKron 1 B) =
      _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron A B) := by
  congr 1
  exact _root_.LIDT.MIPStarRE.LDT.leftTensor_mul_rightTensor_eq_opTensor A B































end MIPStarRE.QPBT.DistanceCalculus

/- Source helpers from QPBT/Combining/ExtendedLineGame/SameLineRejection.lean. -/
/-!
# Same-line branch rejection for the extended direct game

The axis-axis and diagonal-diagonal verifier branches compare the complete
typed coefficient answers returned by the two line measurements. This module
identifies each branch rejection exactly with the corresponding coefficient-
answer consistency defect, averaged over the marginal law of the supplied
line. These are exact transport identities, not numerical passing bounds.

## References

- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1020-1034`
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1279-1288`
- Blueprint `lem:qld-4-7`.
- Issue Dengnifer/MIPStarRE-QPBT-bak#317.
-/

@[expose] public section

open scoped BigOperators MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

namespace ExtendedLineGame

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {epsilon deltaQ deltaL : Real}
variable {setting : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon}
variable {points : _root_.MIPStarRE.QPBT.CombinedPointsWitness setting deltaQ}





private theorem answer_mismatch_eq_consistency
    (D : _root_.MIPStarRE.QPBT.DirectLdParams) {X : Type*} [Fintype X] [DecidableEq X]
    (mu : _root_.LIDT.MIPStarRE.LDT.Distribution X) (S : _root_.MIPStarRE.QPBT.Strategy (_root_.MIPStarRE.QPBT.directLdGame D))
    (qA qB : X -> _root_.MIPStarRE.QPBT.DirectLdQuestion D) :
    _root_.MIPStarRE.QPBT.consistencyDefect mu
        (fun x answer => _root_.MIPStarRE.QPBT.heteroKron ((S.A (qA x)).effect answer) 1)
        (fun x answer => _root_.MIPStarRE.QPBT.heteroKron 1 ((S.B (qB x)).effect answer)) S.ψ =
      _root_.LIDT.MIPStarRE.LDT.avgOver mu (fun x => _root_.MIPStarRE.QPBT.outcomeEventWeight S (qA x) (qB x)
        (fun answerA answerB => answerA ≠ answerB)) := by
  unfold _root_.MIPStarRE.QPBT.consistencyDefect _root_.MIPStarRE.QPBT.outcomeEventWeight
  apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
  intro x
  simp only [_root_.MIPStarRE.QPBT.DistanceCalculus.consistency_term_eq_stateQForm]
  simp_rw [_root_.MIPStarRE.QPBT.DistanceCalculus.placed_product_stateQForm_eq]
  apply Finset.sum_congr rfl
  intro answerA _
  apply Finset.sum_congr rfl
  intro answerB _
  by_cases heq : answerA = answerB
  · simp [heq]
  · simp [heq, _root_.MIPStarRE.QPBT.outcomeWeight, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm]

private theorem sameLine_rejectedMass_eq_answer_mismatch
    (lines : _root_.MIPStarRE.QPBT.ExtendedLinesWitness setting points deltaL)
    (kind : _root_.MIPStarRE.QPBT.LdType) (hkind : kind = .aline ∨ kind = .dline)
    (sample : _root_.MIPStarRE.QPBT.DirectLdSpace P.extendedDirectLd) :
    _root_.MIPStarRE.QPBT.directRejectedMass P.extendedDirectLd (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
        (kind, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd kind sample)
        (kind, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd kind sample) =
      _root_.MIPStarRE.QPBT.outcomeEventWeight (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
        (kind, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd kind sample)
        (kind, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd kind sample)
        (fun answerA answerB => answerA ≠ answerB) := by
  classical
  unfold _root_.MIPStarRE.QPBT.directRejectedMass _root_.MIPStarRE.QPBT.outcomeEventWeight
  apply Finset.sum_congr rfl
  intro answerA _
  apply Finset.sum_congr rfl
  intro answerB _
  by_cases heq : answerA = answerB
  · subst answerB
    by_cases hvalid : _root_.MIPStarRE.QPBT.validDirectLdAnswer kind answerA = true
    · have hwin : _root_.MIPStarRE.QPBT.directLdWinPredicate P.extendedDirectLd
          (kind, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd kind sample)
          (kind, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd kind sample)
          answerA answerA = true := by
        rcases hkind with rfl | rfl <;> cases answerA <;>
          simp_all [_root_.MIPStarRE.QPBT.directLdWinPredicate, _root_.MIPStarRE.QPBT.validDirectLdAnswer]
      simp [hwin]
    · have hvalidFalse : _root_.MIPStarRE.QPBT.validDirectLdAnswer kind answerA = false :=
        Bool.eq_false_of_not_eq_true hvalid
      have hzero := _root_.MIPStarRE.QPBT.ExtendedLineGame.outcomeWeight_eq_zero_of_invalid lines
        (kind, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd kind sample)
        (kind, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd kind sample)
        answerA answerA (Or.inl hvalidFalse)
      simp [hzero]
  · have hnotwin : _root_.MIPStarRE.QPBT.directLdWinPredicate P.extendedDirectLd
        (kind, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd kind sample)
        (kind, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd kind sample)
        answerA answerB ≠ true := by
      intro hwin
      apply heq
      rcases hkind with rfl | rfl <;> cases answerA <;> cases answerB <;>
        simp_all [_root_.MIPStarRE.QPBT.directLdWinPredicate, _root_.MIPStarRE.QPBT.validDirectLdAnswer]
    have hwinFalse : _root_.MIPStarRE.QPBT.directLdWinPredicate P.extendedDirectLd
        (kind, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd kind sample)
        (kind, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd kind sample)
        answerA answerB = false := Bool.eq_false_of_not_eq_true hnotwin
    simp only [hwinFalse, Bool.false_eq_true, if_false]
    split
    · rfl
    · rename_i hnot
      exact (hnot heq).elim

private theorem axis_answer_effect
    (lines : _root_.MIPStarRE.QPBT.ExtendedLinesWitness setting points deltaL) (side : _root_.MIPStarRE.QPBT.PlayerSide)
    (sample : _root_.MIPStarRE.QPBT.DirectLdSpace P.extendedDirectLd)
    (answer : _root_.MIPStarRE.QPBT.DirectLdAnswer P.extendedDirectLd) :
    (_root_.MIPStarRE.QPBT.ExtendedLineGame.answerMeasurement lines side
      (.aline, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .aline sample)).effect answer =
      ((lines.Qline side (_root_.MIPStarRE.QPBT.directALineDescOf P.extendedDirectLd sample)).postprocess
        (_root_.MIPStarRE.QPBT.ExtendedLineGame.axisAnswer P)).effect answer := by
  unfold _root_.MIPStarRE.QPBT.ExtendedLineGame.answerMeasurement
  rw [_root_.MIPStarRE.QPBT.ExtendedLineGame.axis_description_canonical]







end ExtendedLineGame

end

end MIPStarRE.QPBT

/-!
# Same-line branch rejection for the extended direct game

The axis-axis and diagonal-diagonal verifier branches compare the complete
typed coefficient answers returned by the two line measurements. This module
identifies each branch rejection exactly with the corresponding coefficient-
answer consistency defect, averaged over the marginal law of the supplied
line. These are exact transport identities, not numerical passing bounds.

## References

- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1020-1034`
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1279-1288`
- Blueprint `lem:qld-4-7`.
- Issue Dengnifer/MIPStarRE-QPBT-bak#317.
-/



open scoped BigOperators MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum



open MIPStarRE.QPBT.ExtendedLineGame

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {epsilon deltaQ deltaL : Real}
variable {setting : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon}
variable {points : _root_.MIPStarRE.QPBT.CombinedPointsWitness setting deltaQ}

theorem solution
    (lines : _root_.MIPStarRE.QPBT.ExtendedLinesWitness setting points deltaL) :
    _root_.MIPStarRE.QPBT.directLdBranchRejectionProbability P.extendedDirectLd (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
        (.aline, .aline) = _root_.MIPStarRE.QPBT.ExtendedLineGame.axisCoefficientAnswerDefect lines := by
  rw [_root_.MIPStarRE.QPBT.directLdBranchRejectionProbability_eq_avgOver]
  calc
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.DirectLdSpace P.extendedDirectLd))
        (fun sample => _root_.MIPStarRE.QPBT.directRejectedMass P.extendedDirectLd (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
          (.aline, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .aline sample)
          (.aline, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .aline sample)) =
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.DirectLdSpace P.extendedDirectLd))
        (fun sample => _root_.MIPStarRE.QPBT.outcomeEventWeight (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
          (.aline, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .aline sample)
          (.aline, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .aline sample)
          (fun answerA answerB => answerA ≠ answerB)) := by
      apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
      exact sameLine_rejectedMass_eq_answer_mismatch lines .aline (Or.inl rfl)
    _ = _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.DirectLdSpace P.extendedDirectLd))
        (fun sample answer => _root_.MIPStarRE.QPBT.heteroKron
          ((_root_.MIPStarRE.QPBT.ExtendedLineGame.answerMeasurement lines .alice
            (.aline, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .aline sample)).effect answer) 1)
        (fun sample answer => _root_.MIPStarRE.QPBT.heteroKron 1
          ((_root_.MIPStarRE.QPBT.ExtendedLineGame.answerMeasurement lines .bob
            (.aline, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .aline sample)).effect answer))
        (_root_.MIPStarRE.QPBT.ExtendedLineGame.pairState setting) :=
      (answer_mismatch_eq_consistency P.extendedDirectLd _ (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
        (fun sample => (.aline, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .aline sample))
        (fun sample => (.aline, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .aline sample))).symm
    _ = _root_.MIPStarRE.QPBT.ExtendedLineGame.axisCoefficientAnswerDefect lines := by
      unfold _root_.MIPStarRE.QPBT.ExtendedLineGame.axisCoefficientAnswerDefect _root_.MIPStarRE.QPBT.consistencyDefect
      rw [_root_.MIPStarRE.QPBT.directALinePointDist, _root_.MIPStarRE.QPBT.Distribution.map_map, _root_.LIDT.MIPStarRE.LDT.Distribution.avgOver_map]
      apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
      intro sample
      apply Finset.sum_congr rfl
      intro answerA _
      apply Finset.sum_congr rfl
      intro answerB _
      dsimp only
      rw [axis_answer_effect lines .alice sample answerA,
        axis_answer_effect lines .bob sample answerB]
