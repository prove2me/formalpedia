-- Prove2me | solution 1 for MIPStarRE.QPBT.directPointAnswerReadout_eq_of_win
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T20:57:53.787073+00:00
-- url     : https://prove2.me/submissions/6bc80508-846e-4d08-866d-3c35cb4a26f9

-- Generated proof for MIPStarRE.QPBT.directPointAnswerReadout_eq_of_win.
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
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
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

theorem solution (D : _root_.MIPStarRE.QPBT.DirectLdParams) (r : Fin D.k)
    (p : Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D) (a b : _root_.MIPStarRE.QPBT.DirectLdAnswer D)
    (hwin : _root_.MIPStarRE.QPBT.directLdWinPredicate D (_root_.MIPStarRE.QPBT.directLdPointQuestionOf D p)
      (_root_.MIPStarRE.QPBT.directLdPointQuestionOf D p) a b = true) :
    letI := D.toLDTFieldModel
    _root_.MIPStarRE.QPBT.directPointAnswerReadout D r a = _root_.MIPStarRE.QPBT.directPointAnswerReadout D r b := by
  letI := D.toLDTFieldModel
  cases a with
  | pointVals u =>
      cases b with
      | pointVals v =>
          have huv : u = v := by
            simpa [_root_.MIPStarRE.QPBT.directLdWinPredicate, _root_.MIPStarRE.QPBT.directLdPointQuestionOf,
              _root_.MIPStarRE.QPBT.validDirectLdAnswer] using hwin
          subst huv
          rfl
      | alinePolys _ =>
          simp [_root_.MIPStarRE.QPBT.directLdWinPredicate, _root_.MIPStarRE.QPBT.directLdPointQuestionOf,
            _root_.MIPStarRE.QPBT.validDirectLdAnswer] at hwin
      | dlinePolys _ =>
          simp [_root_.MIPStarRE.QPBT.directLdWinPredicate, _root_.MIPStarRE.QPBT.directLdPointQuestionOf,
            _root_.MIPStarRE.QPBT.validDirectLdAnswer] at hwin
  | alinePolys _ =>
      simp [_root_.MIPStarRE.QPBT.directLdWinPredicate, _root_.MIPStarRE.QPBT.directLdPointQuestionOf,
        _root_.MIPStarRE.QPBT.validDirectLdAnswer] at hwin
  | dlinePolys _ =>
      simp [_root_.MIPStarRE.QPBT.directLdWinPredicate, _root_.MIPStarRE.QPBT.directLdPointQuestionOf,
        _root_.MIPStarRE.QPBT.validDirectLdAnswer] at hwin
