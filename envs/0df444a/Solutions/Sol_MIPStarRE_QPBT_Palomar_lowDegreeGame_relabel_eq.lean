-- Prove2me | solution 1 for MIPStarRE.QPBT.Palomar.lowDegreeGame_relabel_eq
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T00:56:54.332217+00:00
-- url     : https://prove2.me/submissions/88950c2f-68da-43d8-b330-ab7bbbfe2f77

-- Generated proof for MIPStarRE.QPBT.Palomar.lowDegreeGame_relabel_eq.
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
import Definitions.Def_QPBT_QPBT_Palomar_Bridge
import Definitions.Def_QPBT_QPBT_Palomar_Definitions
import Definitions.Def_QPBT_QPBT_Palomar_LowDegreeGameBridge
import Definitions.Def_QPBT_QPBT_Palomar_LowDegreeGameStrategyBridge
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Mathlib
import Theorems.Thm_MIPStarRE_QPBT_Palomar_lowDegreeQuestionPMF_map
import Theorems.Thm_MIPStarRE_QPBT_Palomar_lowDegreeWin_equiv

namespace MIPStarRE.QPBT.Palomar
end MIPStarRE.QPBT.Palomar
namespace MIPStarRE.QPBT.Palomar.Game
end MIPStarRE.QPBT.Palomar.Game
namespace MIPStarRE.QPBT.Palomar.POVM
end MIPStarRE.QPBT.Palomar.POVM
namespace MIPStarRE.QPBT.Palomar.Strategy
end MIPStarRE.QPBT.Palomar.Strategy

/-!
# Strategy bridge for the compact low individual degree game

This module transports compact strategies across the exact question and answer
equivalences of `LowDegreeGameBridge`.  The transported game is the existing
low-degree game, and every compact strategy has exactly the same Born value
after conversion through the Palomar foundation bridge.

## References

`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-440`.
-/



open scoped BigOperators

open MIPStarRE.QPBT.Palomar



open MIPStarRE.QPBT.Palomar.POVM









open MIPStarRE.QPBT.Palomar.Game







open MIPStarRE.QPBT.Palomar.Strategy

theorem solution (P : _root_.MIPStarRE.QPBT.LdParams) :
    _root_.MIPStarRE.QPBT.Palomar.Game.relabel
        (_root_.MIPStarRE.QPBT.Palomar.lowDegreeGame (_root_.MIPStarRE.QPBT.Palomar.LowDegreeParams.ofLdParams P)
          (_root_.MIPStarRE.QPBT.binaryRepresentation P.model))
        (_root_.MIPStarRE.QPBT.Palomar.lowDegreeQuestionEquiv P) (_root_.MIPStarRE.QPBT.Palomar.lowDegreeQuestionEquiv P)
        (_root_.MIPStarRE.QPBT.Palomar.lowDegreeAnswerEquiv P) (_root_.MIPStarRE.QPBT.Palomar.lowDegreeAnswerEquiv P) =
      _root_.MIPStarRE.QPBT.Palomar.Game.ofGame (_root_.MIPStarRE.QPBT.ldGame P) := by
  apply _root_.MIPStarRE.QPBT.Palomar.Game.ext
  · exact _root_.MIPStarRE.QPBT.Palomar.lowDegreeQuestionPMF_map P
  · funext x y a b
    change _root_.MIPStarRE.QPBT.Palomar.lowDegreeWin (_root_.MIPStarRE.QPBT.Palomar.LowDegreeParams.ofLdParams P)
        (_root_.MIPStarRE.QPBT.binaryRepresentation P.model)
        ((_root_.MIPStarRE.QPBT.Palomar.lowDegreeQuestionEquiv P).symm x) ((_root_.MIPStarRE.QPBT.Palomar.lowDegreeQuestionEquiv P).symm y)
        ((_root_.MIPStarRE.QPBT.Palomar.lowDegreeAnswerEquiv P).symm a) ((_root_.MIPStarRE.QPBT.Palomar.lowDegreeAnswerEquiv P).symm b) =
      _root_.MIPStarRE.QPBT.ldWinPredicate P x y a b
    simpa using _root_.MIPStarRE.QPBT.Palomar.lowDegreeWin_equiv P
      ((_root_.MIPStarRE.QPBT.Palomar.lowDegreeQuestionEquiv P).symm x) ((_root_.MIPStarRE.QPBT.Palomar.lowDegreeQuestionEquiv P).symm y)
      ((_root_.MIPStarRE.QPBT.Palomar.lowDegreeAnswerEquiv P).symm a) ((_root_.MIPStarRE.QPBT.Palomar.lowDegreeAnswerEquiv P).symm b)
