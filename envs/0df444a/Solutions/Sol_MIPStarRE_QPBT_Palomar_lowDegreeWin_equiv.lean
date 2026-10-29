-- Prove2me | solution 1 for MIPStarRE.QPBT.Palomar.lowDegreeWin_equiv
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T00:51:20.820389+00:00
-- url     : https://prove2.me/submissions/7769f639-bcef-4045-a8ce-e97fd8042b60

-- Generated proof for MIPStarRE.QPBT.Palomar.lowDegreeWin_equiv.
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
import Definitions.Def_QPBT_QPBT_Palomar_Definitions
import Definitions.Def_QPBT_QPBT_Palomar_LowDegreeGameBridge
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Mathlib

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace MIPStarRE.QPBT.Palomar
end MIPStarRE.QPBT.Palomar

/-!
# Exact bridge for the compact low individual degree game

This module identifies the compact product-space game with the existing
low-degree game.  The bridge is by explicit equivalences of question
coordinates and answer summands.  It preserves the question PMF, every branch
of the Boolean verifier, and the value of every compact strategy exactly.

## References

`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-440`.
-/



open scoped BigOperators

open MIPStarRE.QPBT.Palomar

open LIDT.MIPStarRE.LDT

theorem solution (P : _root_.MIPStarRE.QPBT.LdParams)
    (x y : _root_.MIPStarRE.QPBT.Palomar.LowDegreeQuestion (_root_.MIPStarRE.QPBT.Palomar.LowDegreeParams.ofLdParams P)
      (_root_.MIPStarRE.QPBT.ScalarQ P))
    (a b : _root_.MIPStarRE.QPBT.Palomar.LowDegreeAnswer (_root_.MIPStarRE.QPBT.Palomar.LowDegreeParams.ofLdParams P)
      (_root_.MIPStarRE.QPBT.ScalarQ P)) :
    _root_.MIPStarRE.QPBT.Palomar.lowDegreeWin (_root_.MIPStarRE.QPBT.Palomar.LowDegreeParams.ofLdParams P)
        (_root_.MIPStarRE.QPBT.binaryRepresentation P.model) x y a b =
      _root_.MIPStarRE.QPBT.ldWinPredicate P (_root_.MIPStarRE.QPBT.Palomar.lowDegreeQuestionEquiv P x)
        (_root_.MIPStarRE.QPBT.Palomar.lowDegreeQuestionEquiv P y) (_root_.MIPStarRE.QPBT.Palomar.lowDegreeAnswerEquiv P a)
        (_root_.MIPStarRE.QPBT.Palomar.lowDegreeAnswerEquiv P b) := by
  rcases x with ⟨tA, xA⟩
  rcases y with ⟨tB, xB⟩
  rcases a with a | (a | a) <;>
    rcases b with b | (b | b) <;>
      cases tA <;> cases tB <;>
        simp [_root_.MIPStarRE.QPBT.Palomar.lowDegreeWin, _root_.MIPStarRE.QPBT.Palomar.validLowDegreeAnswer, _root_.MIPStarRE.QPBT.ldWinPredicate,
          _root_.MIPStarRE.QPBT.validLdAnswer, _root_.MIPStarRE.QPBT.Palomar.lowDegreeQuestionEquiv,
          _root_.MIPStarRE.QPBT.Palomar.lowDegreeAnswerEquiv, _root_.MIPStarRE.QPBT.ldAnswerEquiv,
          _root_.MIPStarRE.QPBT.Palomar.lowDegreeTypeEquiv, _root_.MIPStarRE.QPBT.alinePointCondition,
          _root_.MIPStarRE.QPBT.dlinePointCondition, _root_.MIPStarRE.QPBT.coordinateDirection] <;>
        rfl
