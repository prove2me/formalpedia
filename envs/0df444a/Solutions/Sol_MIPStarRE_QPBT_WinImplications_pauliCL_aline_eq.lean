-- Prove2me | solution 1 for MIPStarRE.QPBT.WinImplications.pauliCL_aline_eq
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T00:28:55.727979+00:00
-- url     : https://prove2.me/submissions/f6676753-a88e-4162-842e-5bdae61e45f1

-- Generated proof for MIPStarRE.QPBT.WinImplications.pauliCL_aline_eq.
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
import Definitions.Def_QPBT_QPBT_Algebra_Lines
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_LineDefs
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_LowDegree
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.WinImplications
end MIPStarRE.QPBT.WinImplications

/-!
# Low-degree winning implications

This module proves the exact line-point and Pauli-basis consistency bounds.

## References

The line-point and Pauli-basis consistency theorems prove items 2 and 3
of `lem:qld-win-implications`
from `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:192-267`
and blueprint `lem:qld-win-implications` and `lem:qld-win-implications-obs`.
-/



open scoped BigOperators Matrix ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum



open MIPStarRE.QPBT.WinImplications
attribute [local instance] _root_.MIPStarRE.QPBT.WinImplications.instDecidableRel_qPBT
attribute [local instance] _root_.MIPStarRE.QPBT.WinImplications.linePointFintypeCanonical

theorem solution (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (W : _root_.MIPStarRE.QPBT.PauliKind)
    (z : _root_.MIPStarRE.QPBT.PauliSpace P) :
    _root_.MIPStarRE.QPBT.pauliCL P (.aline W) z = _root_.MIPStarRE.QPBT.ProjectiveSetting.contentOfLine P W
      (_root_.MIPStarRE.QPBT.aLineDescOf P.toLdParams (_root_.MIPStarRE.QPBT.ldALineCL P.toLdParams (_root_.MIPStarRE.QPBT.pauliToLd P W z))) := by
  apply congrArg (_root_.MIPStarRE.QPBT.embedLd P W)
  funext i
  rcases i with (j | u) | j
  · change (_root_.MIPStarRE.QPBT.lineRepMap
        (_root_.MIPStarRE.QPBT.coordinateDirection (_root_.MIPStarRE.QPBT.chiIndex P.toLdParams (_root_.MIPStarRE.QPBT.pauliToLd P W z).seed))
        (_root_.MIPStarRE.QPBT.pauliToLd P W z).point) j =
      (_root_.MIPStarRE.QPBT.lineRepMap
        (_root_.MIPStarRE.QPBT.coordinateDirection (_root_.MIPStarRE.QPBT.chiIndex P.toLdParams (_root_.MIPStarRE.QPBT.pauliToLd P W z).seed))
        (_root_.MIPStarRE.QPBT.lineRepMap
          (_root_.MIPStarRE.QPBT.coordinateDirection (_root_.MIPStarRE.QPBT.chiIndex P.toLdParams (_root_.MIPStarRE.QPBT.pauliToLd P W z).seed))
          (_root_.MIPStarRE.QPBT.pauliToLd P W z).point)) j
    rw [_root_.MIPStarRE.QPBT.lineRepMap_apply_self]
  · rfl
  · rfl
