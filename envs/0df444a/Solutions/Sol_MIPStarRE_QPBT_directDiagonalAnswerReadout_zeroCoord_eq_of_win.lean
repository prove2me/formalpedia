-- Prove2me | solution 1 for MIPStarRE.QPBT.directDiagonalAnswerReadout_zeroCoord_eq_of_win
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T21:01:20.698234+00:00
-- url     : https://prove2.me/submissions/27e11622-d06c-479c-a09e-d7895e22f334

-- Generated proof for MIPStarRE.QPBT.directDiagonalAnswerReadout_zeroCoord_eq_of_win.
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
import Definitions.Def_QPBT_QPBT_Algebra_Coefficients
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_Lines
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Game
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Correspondence
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Questions
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Mathlib

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/DirectLowDegree/Transport/Correspondence.lean. -/
/-!
# Question correspondence for the directly indexed low-degree game

The finite-field coordinates, polynomial answers, and question law of the
directly indexed game are equivalent to their seed-indexed and low individual
degree counterparts.

## References

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-458`
- `references/ldt-paper/test_definition.tex:98-151`
- `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`
-/

@[expose] public section

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.Quantum

noncomputable section

/-! ## Parameters and finite-field coordinates -/













/-! ## Bounded coefficient vectors -/







private theorem coefficientPolynomial_eval
    {K : Type*} [Field K] (n : ℕ) (c : Fin (n + 1) → K) (t : K) :
    (_root_.MIPStarRE.QPBT.coefficientPolynomial n c).eval t = _root_.MIPStarRE.QPBT.evalCoefficient c t := by
  simpa [_root_.MIPStarRE.QPBT.coefficientPolynomial, _root_.MIPStarRE.QPBT.evalCoefficient] using
    (Polynomial.eval_eq_sum_degreeLTEquiv
      (((Polynomial.degreeLTEquiv K (n + 1)).symm c).2) t)







/-- Coefficient evaluation agrees with evaluation of the corresponding LDT
diagonal-line polynomial. -/
theorem directDiagonalAnswerEquiv_apply (D : _root_.MIPStarRE.QPBT.DirectLdParams)
    (c : _root_.MIPStarRE.QPBT.DirectDegPoly D (D.m * D.d)) (t : _root_.MIPStarRE.QPBT.DirectScalarQ D) :
    letI := D.toLDTFieldModel
    _root_.MIPStarRE.QPBT.directDiagonalAnswerEquiv D c (_root_.MIPStarRE.QPBT.directScalarEquiv D t) =
      _root_.MIPStarRE.QPBT.directScalarEquiv D (_root_.MIPStarRE.QPBT.evalCoefficient c t) := by
  letI := D.toLDTFieldModel
  simp only [_root_.MIPStarRE.QPBT.directDiagonalAnswerEquiv, _root_.LIDT.MIPStarRE.LDT.DiagonalLinePolynomial.toFun,
    evalLinePolynomialModel]
  rw [show _root_.LIDT.MIPStarRE.LDT.decodeScalar (_root_.MIPStarRE.QPBT.directScalarEquiv D t) = t by
    exact (_root_.LIDT.MIPStarRE.LDT.FieldModel.equiv (q := D.q)).symm_apply_apply t]
  change _root_.LIDT.MIPStarRE.LDT.encodeScalar ((_root_.MIPStarRE.QPBT.coefficientPolynomial (D.m * D.d) c).eval t) =
    _root_.MIPStarRE.QPBT.directScalarEquiv D (_root_.MIPStarRE.QPBT.evalCoefficient c t)
  exact congrArg (_root_.LIDT.MIPStarRE.LDT.FieldModel.equiv (q := D.q))
    (coefficientPolynomial_eval (D.m * D.d) c t)

/-! ## Parameters and answers of the two QPBT game presentations -/







/-! ## Parsing seed-indexed questions -/

















/-! ## Exact question-law transport -/











end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/DirectLowDegree/Transport/Questions.lean. -/
/-!
# Question and answer transport for the directly indexed low-degree game

This module reads low individual degree test questions as canonical direct
questions and rebases direct answers to the LDT line parametrization.

Points and lines are decoded with the coordinate order reversed
(`directPointEquiv`), so that the suffix-zero direction restriction of the
LDT diagonal test becomes the prefix-zero restriction of the direct game.
An LDT diagonal line reveals no coordinate index, whereas a direct diagonal
question carries one.  The transported question uses the *leading index* of
the decoded direction, the least coordinate at which the direction is
nonzero.  Under the direct sampler, this is the index attached to the sampled
direction exactly when the direction is nonzero at the sampled index
(`directDiagonalIndexOf_prefixProjection`), an event of conditional
probability `1 - 1/q`; on the LDT side, the leading index of a decoded
`j`-restricted direction is `Fin.rev j` exactly when its pivot coordinate is
nonzero (`directDiagonalIndexOf_extendRestrictedDirection`).  Diagonal answers
on zero-direction lines are read as the constant polynomial carrying their
value at the base point, following `rem:ld-win-zero-direction`.

## References

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:230-272`
- `references/ldt-paper/test_definition.tex:49-65`
- `rem:ld-win-zero-direction`
- `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`
-/

@[expose] public section

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.Quantum

noncomputable section

/-! ## Canonical line rebasing of LDT lines -/











/-! ## The leading index of a direction -/















/-! ## Decoding LDT points and lines -/



















/-! ## Rebasing lines -/





















/-! ## Reading direct answers as LDT answers -/





/-- A constant answer evaluates to its value at every parameter. -/
theorem constantDiagonalAnswer_apply (D : _root_.MIPStarRE.QPBT.DirectLdParams)
    (x : _root_.MIPStarRE.QPBT.DirectScalarQ D) (t : _root_.LIDT.MIPStarRE.LDT.Fq D.toLDTParameters) :
    letI := D.toLDTFieldModel
    _root_.MIPStarRE.QPBT.constantDiagonalAnswer D x t = _root_.MIPStarRE.QPBT.directScalarEquiv D x := by
  letI := D.toLDTFieldModel
  change _root_.LIDT.MIPStarRE.LDT.encodeScalar ((Polynomial.C x).eval (_root_.LIDT.MIPStarRE.LDT.decodeScalar t)) =
    _root_.MIPStarRE.QPBT.directScalarEquiv D x
  rw [Polynomial.eval_C]
  rfl











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









/-! ## Accepted answer pairs read out consistently

An accepted answer pair of the direct game consists of well-formed answers
satisfying the line-versus-point clause or the consistency clause of
`def:ld-win-predicate`.  The readouts of `Transport.Questions` evaluate the
rebased line polynomial at the LDT base point, which is the direct point
at the canonical rebase parameter; the accepted clause forces this value to
be the point answer.  Zero directions use the constant readout at the base
point, where the universal clause of `rem:ld-win-zero-direction` gives the
value at parameter zero. -/





/-- The diagonal-line acceptance clause gives the readout its point value at
the LDT base point, using the canonical rebase parameter for a nonzero
direction and the parameter zero for the zero direction. -/
private theorem diagonal_readout_of_condition (D : _root_.MIPStarRE.QPBT.DirectLdParams) (r : Fin D.k)
    (line : _root_.LIDT.MIPStarRE.LDT.DiagonalLine D.toLDTParameters)
    (f : Fin D.k → Fin (D.m * D.d + 1) → _root_.MIPStarRE.QPBT.DirectScalarQ D)
    (c : Fin D.k → _root_.MIPStarRE.QPBT.DirectScalarQ D)
    (hcond : _root_.MIPStarRE.QPBT.directDlinePointCondition D
      ⟨_root_.MIPStarRE.QPBT.lineRepMap (_root_.MIPStarRE.QPBT.ldtPointToDirect D line.direction) (_root_.MIPStarRE.QPBT.ldtPointToDirect D line.base),
        _root_.MIPStarRE.QPBT.directDiagonalIndexOf D (_root_.MIPStarRE.QPBT.ldtPointToDirect D line.direction),
        _root_.MIPStarRE.QPBT.ldtPointToDirect D line.direction⟩
      ⟨_root_.MIPStarRE.QPBT.ldtPointToDirect D line.base, D.firstIndex, 0⟩ f c) :
    letI := D.toLDTFieldModel
    _root_.MIPStarRE.QPBT.directDiagonalAnswerReadout D r line (.dlinePolys f) _root_.LIDT.MIPStarRE.LDT.zeroCoord =
      _root_.MIPStarRE.QPBT.directScalarEquiv D (c r) := by
  letI := D.toLDTFieldModel
  by_cases hdir : _root_.MIPStarRE.QPBT.ldtPointToDirect D line.direction = 0
  · have hbase : _root_.MIPStarRE.QPBT.ldtPointToDirect D line.base =
        _root_.MIPStarRE.QPBT.lineRepMap (0 : Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D) (_root_.MIPStarRE.QPBT.ldtPointToDirect D line.base) := by
      have hspec := _root_.MIPStarRE.QPBT.directLineRepParameter_spec
        (_root_.MIPStarRE.QPBT.ldtPointToDirect D line.direction) (_root_.MIPStarRE.QPBT.ldtPointToDirect D line.base)
      rwa [hdir, smul_zero, add_zero] at hspec
    rw [hdir] at hcond
    have heval : _root_.MIPStarRE.QPBT.evalCoefficient (f r) 0 = c r := by
      refine hcond 0 ?_ r
      change _root_.MIPStarRE.QPBT.ldtPointToDirect D line.base =
        _root_.MIPStarRE.QPBT.lineRepMap (0 : Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D) (_root_.MIPStarRE.QPBT.ldtPointToDirect D line.base) +
          (0 : _root_.MIPStarRE.QPBT.DirectScalarQ D) • (0 : Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D)
      rw [smul_zero, add_zero]
      exact hbase
    simp only [_root_.MIPStarRE.QPBT.directDiagonalAnswerReadout, hdir, if_true]
    rw [_root_.MIPStarRE.QPBT.constantDiagonalAnswer_apply, heval]
  · have heval :
        _root_.MIPStarRE.QPBT.evalCoefficient (f r) (_root_.MIPStarRE.QPBT.directDiagonalRebaseParameter D line) = c r :=
      hcond (_root_.MIPStarRE.QPBT.directDiagonalRebaseParameter D line)
        (_root_.MIPStarRE.QPBT.directLineRepParameter_spec
          (_root_.MIPStarRE.QPBT.ldtPointToDirect D line.direction) (_root_.MIPStarRE.QPBT.ldtPointToDirect D line.base)) r
    simp only [_root_.MIPStarRE.QPBT.directDiagonalAnswerReadout, hdir, if_false]
    rw [_root_.LIDT.MIPStarRE.LDT.DiagonalLinePolynomial.reparamAt_apply_zero,
      _root_.MIPStarRE.QPBT.directDiagonalAnswerEquiv_apply, heval]









/-! ## Direct samples as products -/



/-! ## The point-agreement and axis-line branches -/



end

end MIPStarRE.QPBT

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



open scoped BigOperators MatrixOrder Matrix ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.Quantum





/-! ## Rejected Born mass at a fixed question pair -/









/-! ## Accepted answer pairs read out consistently

An accepted answer pair of the direct game consists of well-formed answers
satisfying the line-versus-point clause or the consistency clause of
`def:ld-win-predicate`.  The readouts of `Transport.Questions` evaluate the
rebased line polynomial at the LDT base point, which is the direct point
at the canonical rebase parameter; the accepted clause forces this value to
be the point answer.  Zero directions use the constant readout at the base
point, where the universal clause of `rem:ld-win-zero-direction` gives the
value at parameter zero. -/

theorem solution (D : _root_.MIPStarRE.QPBT.DirectLdParams)
    (r : Fin D.k) (line : _root_.LIDT.MIPStarRE.LDT.DiagonalLine D.toLDTParameters)
    (a b : _root_.MIPStarRE.QPBT.DirectLdAnswer D)
    (hwin : _root_.MIPStarRE.QPBT.directLdWinPredicate D (_root_.MIPStarRE.QPBT.directDiagonalQuestionOf D line)
      (_root_.MIPStarRE.QPBT.directPointQuestionOf D line.base) a b = true) :
    letI := D.toLDTFieldModel
    _root_.MIPStarRE.QPBT.directDiagonalAnswerReadout D r line a _root_.LIDT.MIPStarRE.LDT.zeroCoord =
      _root_.MIPStarRE.QPBT.directPointAnswerReadout D r b := by
  letI := D.toLDTFieldModel
  cases a with
  | dlinePolys f =>
      cases b with
      | pointVals c =>
          refine diagonal_readout_of_condition D r line f c ?_
          have hcondition := hwin
          simp only [_root_.MIPStarRE.QPBT.directLdWinPredicate, _root_.MIPStarRE.QPBT.directDiagonalQuestionOf,
            _root_.MIPStarRE.QPBT.directPointQuestionOf, _root_.MIPStarRE.QPBT.directLdPointQuestionOf,
            _root_.MIPStarRE.QPBT.validDirectLdAnswer, Bool.and_self, ↓reduceIte] at hcondition
          exact @of_decide_eq_true _ (Classical.propDecidable _) hcondition
      | alinePolys _ =>
          simp [_root_.MIPStarRE.QPBT.directLdWinPredicate, _root_.MIPStarRE.QPBT.directDiagonalQuestionOf, _root_.MIPStarRE.QPBT.directPointQuestionOf,
            _root_.MIPStarRE.QPBT.directLdPointQuestionOf, _root_.MIPStarRE.QPBT.validDirectLdAnswer] at hwin
      | dlinePolys _ =>
          simp [_root_.MIPStarRE.QPBT.directLdWinPredicate, _root_.MIPStarRE.QPBT.directDiagonalQuestionOf, _root_.MIPStarRE.QPBT.directPointQuestionOf,
            _root_.MIPStarRE.QPBT.directLdPointQuestionOf, _root_.MIPStarRE.QPBT.validDirectLdAnswer] at hwin
  | pointVals _ =>
      simp [_root_.MIPStarRE.QPBT.directLdWinPredicate, _root_.MIPStarRE.QPBT.directDiagonalQuestionOf, _root_.MIPStarRE.QPBT.directPointQuestionOf,
        _root_.MIPStarRE.QPBT.directLdPointQuestionOf, _root_.MIPStarRE.QPBT.validDirectLdAnswer] at hwin
  | alinePolys _ =>
      simp [_root_.MIPStarRE.QPBT.directLdWinPredicate, _root_.MIPStarRE.QPBT.directDiagonalQuestionOf, _root_.MIPStarRE.QPBT.directPointQuestionOf,
        _root_.MIPStarRE.QPBT.directLdPointQuestionOf, _root_.MIPStarRE.QPBT.validDirectLdAnswer] at hwin
