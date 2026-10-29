-- Prove2me | solution 1 for MIPStarRE.QPBT.WinImplications.aline_winning_condition
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T00:33:09.811984+00:00
-- url     : https://prove2.me/submissions/a039fc54-d08d-45bd-98e9-72c99c7efcd5

-- Generated proof for MIPStarRE.QPBT.WinImplications.aline_winning_condition.
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
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_LineDefs
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_LowDegree
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Definitions.Def_QPBT_QPBT_Test_MagicSquare
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Theorems.Thm_MIPStarRE_QPBT_WinImplications_pauliCL_aline_eq

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.WinImplications
end MIPStarRE.QPBT.WinImplications

/- Source helpers from QPBT/Observables/WinImplications/LowDegree.lean. -/
attribute [local instance] _root_.MIPStarRE.QPBT.WinImplications.instDecidableRel_qPBT
attribute [local instance] _root_.MIPStarRE.QPBT.WinImplications.linePointFintypeCanonical
/-!
# Low-degree winning implications

This module proves the exact line-point and Pauli-basis consistency bounds.

## References

The line-point and Pauli-basis consistency theorems prove items 2 and 3
of `lem:qld-win-implications`
from `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:192-267`
and blueprint `lem:qld-win-implications` and `lem:qld-win-implications-obs`.
-/

@[expose] public section

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

namespace WinImplications





















/-- The point conditioning map produces the typed point content. -/
theorem pauliCL_point_eq (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (W : _root_.MIPStarRE.QPBT.PauliKind)
    (z : _root_.MIPStarRE.QPBT.PauliSpace P) :
    _root_.MIPStarRE.QPBT.pauliCL P (.point W) z =
      _root_.MIPStarRE.QPBT.ProjectiveSetting.contentOfPoint P W (_root_.MIPStarRE.QPBT.pauliToLd P W z).point := by
  funext i
  rcases i with ((((j | j) | u) | j) | u) | u <;> cases W <;> rfl



/-- Reading a typed point content recovers its point block. -/
theorem pauliPointBlock_contentOfPoint (P : _root_.MIPStarRE.QPBT.AdmissibleParams)
    (W : _root_.MIPStarRE.QPBT.PauliKind) (u : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) :
    _root_.MIPStarRE.QPBT.pauliPointBlock W (_root_.MIPStarRE.QPBT.ProjectiveSetting.contentOfPoint P W u) = u := by
  funext j
  cases W <;> rfl

/-- Reading a typed line content recovers its canonical base. -/
theorem pauliPointBlock_contentOfLine (P : _root_.MIPStarRE.QPBT.AdmissibleParams)
    (W : _root_.MIPStarRE.QPBT.PauliKind) (line : _root_.MIPStarRE.QPBT.LineDesc P.toLdParams) :
    _root_.MIPStarRE.QPBT.pauliPointBlock W (_root_.MIPStarRE.QPBT.ProjectiveSetting.contentOfLine P W line) = line.base := by
  funext j
  cases W <;> rfl

/-- Reading a typed line content recovers its seed. -/
theorem pauliScalarBlock_contentOfLine (P : _root_.MIPStarRE.QPBT.AdmissibleParams)
    (W : _root_.MIPStarRE.QPBT.PauliKind) (line : _root_.MIPStarRE.QPBT.LineDesc P.toLdParams) :
    _root_.MIPStarRE.QPBT.pauliScalarBlock (_root_.MIPStarRE.QPBT.ProjectiveSetting.contentOfLine P W line) = line.seed := by
  cases W <;> rfl
































































end WinImplications

end

end MIPStarRE.QPBT

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
    (z : _root_.MIPStarRE.QPBT.PauliSpace P) (f : Fin (P.d + 1) → _root_.MIPStarRE.QPBT.PauliScalar P)
    (a : _root_.MIPStarRE.QPBT.PauliScalar P)
    (hwin : _root_.MIPStarRE.QPBT.pauliWinPredicate P
      ((.aline W), _root_.MIPStarRE.QPBT.pauliCL P (.aline W) z)
      ((.point W), _root_.MIPStarRE.QPBT.pauliCL P (.point W) z)
      (.alinePoly f) (.value a) = true) :
    ∀ t : _root_.MIPStarRE.QPBT.ScalarQ P.toLdParams,
      (_root_.MIPStarRE.QPBT.pauliToLd P W z).point =
          (_root_.MIPStarRE.QPBT.aLineDescOf P.toLdParams
            (_root_.MIPStarRE.QPBT.ldALineCL P.toLdParams (_root_.MIPStarRE.QPBT.pauliToLd P W z))).base +
            t • (_root_.MIPStarRE.QPBT.aLineDescOf P.toLdParams
              (_root_.MIPStarRE.QPBT.ldALineCL P.toLdParams (_root_.MIPStarRE.QPBT.pauliToLd P W z))).direction →
        _root_.MIPStarRE.QPBT.evalCoefficient f t = a := by
  rw [_root_.MIPStarRE.QPBT.WinImplications.pauliCL_aline_eq, _root_.MIPStarRE.QPBT.WinImplications.pauliCL_point_eq] at hwin
  have hc : _root_.MIPStarRE.QPBT.pauliAlinePointCondition P W
      (_root_.MIPStarRE.QPBT.ProjectiveSetting.contentOfLine P W
        (_root_.MIPStarRE.QPBT.aLineDescOf P.toLdParams (_root_.MIPStarRE.QPBT.ldALineCL P.toLdParams (_root_.MIPStarRE.QPBT.pauliToLd P W z))))
      (_root_.MIPStarRE.QPBT.ProjectiveSetting.contentOfPoint P W (_root_.MIPStarRE.QPBT.pauliToLd P W z).point) f a := by
    simpa [_root_.MIPStarRE.QPBT.pauliWinPredicate, _root_.MIPStarRE.QPBT.validPauliAnswer] using hwin
  intro t ht
  apply hc t
  rw [_root_.MIPStarRE.QPBT.WinImplications.pauliPointBlock_contentOfPoint, _root_.MIPStarRE.QPBT.WinImplications.pauliPointBlock_contentOfLine,
    _root_.MIPStarRE.QPBT.WinImplications.pauliScalarBlock_contentOfLine]
  funext j
  exact congrFun ht j
