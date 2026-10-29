-- Prove2me | solution 1 for MIPStarRE.QPBT.WinImplications.pointMsLabels_eq_of_win
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T00:37:06.226554+00:00
-- url     : https://prove2.me/submissions/7cc67eee-7120-4ef9-9dc7-d1c71e8e1ff5

-- Generated proof for MIPStarRE.QPBT.WinImplications.pointMsLabels_eq_of_win.
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
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Observables_Anticommuting
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_Commuting
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_LowDegree
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_MagicSquare
import Definitions.Def_QPBT_QPBT_Test_MagicSquare
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























/-- The shared conditioning map produces the typed tuple content. -/
theorem pauliCL_shared_eq (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (t : _root_.MIPStarRE.QPBT.PauliType)
    (ht : _root_.MIPStarRE.QPBT.pauliCL P t = _root_.MIPStarRE.QPBT.pauliSharedProjection) (z : _root_.MIPStarRE.QPBT.PauliSpace P) :
    _root_.MIPStarRE.QPBT.pauliCL P t z = _root_.MIPStarRE.QPBT.ProjectiveSetting.contentOfTuple P
      (_root_.MIPStarRE.QPBT.pauliXBlock z) (_root_.MIPStarRE.QPBT.pauliZBlock z) (_root_.MIPStarRE.QPBT.pauliRXBlock z) (_root_.MIPStarRE.QPBT.pauliRZBlock z) := by
  rw [ht]
  funext i
  rcases i with ((((j | j) | u) | j) | u) | u <;> rfl






































































end WinImplications

end

end MIPStarRE.QPBT

/-!
# Magic Square winning implications

This module proves the exact induced Magic Square value and variable
consistency bounds on anticommuting Pauli tuples.

## References

The Magic Square value and consistency theorems prove items 6 and 7
of `lem:qld-win-implications`
from `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:192-267`
and blueprint `lem:qld-win-implications` and `lem:qld-win-implications-obs`.
-/



open scoped BigOperators Matrix ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum



open MIPStarRE.QPBT.WinImplications

theorem solution (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (W : _root_.MIPStarRE.QPBT.PauliKind)
    (z : _root_.MIPStarRE.QPBT.PauliSpace P) (A B : _root_.MIPStarRE.QPBT.PauliAnswer P)
    (hanti : _root_.MIPStarRE.QPBT.IsAnticommuting (_root_.MIPStarRE.QPBT.WinImplications.pauliSharedSplit P z).1)
    (hwin : _root_.MIPStarRE.QPBT.pauliWinPredicate P
      ((.point W), _root_.MIPStarRE.QPBT.pauliCL P (.point W) z)
      ((.ms (.var (_root_.MIPStarRE.QPBT.WinImplications.selectedMsVar W))),
        _root_.MIPStarRE.QPBT.pauliCL P (.ms (.var (_root_.MIPStarRE.QPBT.WinImplications.selectedMsVar W))) z) A B = true) :
    _root_.MIPStarRE.QPBT.WinImplications.pointTraceLabel P W (_root_.MIPStarRE.QPBT.WinImplications.pauliSharedSplit P z).1 A =
      _root_.MIPStarRE.QPBT.ProjectiveSetting.pairWAnswerOrZero B := by
  cases A <;> cases B <;>
    simp only [_root_.MIPStarRE.QPBT.pauliWinPredicate, _root_.MIPStarRE.QPBT.validPauliAnswer, Bool.and_true,
      Bool.and_self, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
      reduceCtorEq, decide_eq_true_eq] at hwin
  rename_i a bit
  simp only [_root_.MIPStarRE.QPBT.WinImplications.pointTraceLabel, _root_.MIPStarRE.QPBT.ProjectiveSetting.pointAnswerOrZero,
    _root_.MIPStarRE.QPBT.ProjectiveSetting.pairWAnswerOrZero]
  have hgamma : _root_.MIPStarRE.QPBT.pauliPairGamma P
      (_root_.MIPStarRE.QPBT.pauliCL P (.ms (.var (_root_.MIPStarRE.QPBT.WinImplications.selectedMsVar W))) z) ≠ 0 := by
    change _root_.MIPStarRE.QPBT.gammaValue P (_root_.MIPStarRE.QPBT.pauliXBlock z) (_root_.MIPStarRE.QPBT.pauliZBlock z)
      (_root_.MIPStarRE.QPBT.pauliRXBlock z) (_root_.MIPStarRE.QPBT.pauliRZBlock z) ≠ 0 at hanti
    rw [_root_.MIPStarRE.QPBT.WinImplications.pauliCL_shared_eq P (.ms (.var (_root_.MIPStarRE.QPBT.WinImplications.selectedMsVar W))) rfl]
    change _root_.MIPStarRE.QPBT.gammaValue P (_root_.MIPStarRE.QPBT.pauliXBlock z) (_root_.MIPStarRE.QPBT.pauliZBlock z)
      (_root_.MIPStarRE.QPBT.pauliRXBlock z) (_root_.MIPStarRE.QPBT.pauliRZBlock z) ≠ 0
    exact hanti
  rw [_root_.MIPStarRE.QPBT.WinImplications.pauliCL_shared_eq P (.ms (.var (_root_.MIPStarRE.QPBT.WinImplications.selectedMsVar W))) rfl] at hgamma
  rw [_root_.MIPStarRE.QPBT.WinImplications.pauliCL_shared_eq P (.ms (.var (_root_.MIPStarRE.QPBT.WinImplications.selectedMsVar W))) rfl] at hwin
  cases W with
  | X =>
      simp only [_root_.MIPStarRE.QPBT.pauliPointVariableCondition] at hwin
      rcases hwin with hzero | hrest
      · exact (hgamma hzero).elim
      · rcases hrest with hX | hZ
        · simpa [_root_.MIPStarRE.QPBT.WinImplications.selectedTupleScalar, _root_.MIPStarRE.QPBT.WinImplications.pauliSharedSplit, _root_.MIPStarRE.QPBT.pauliRXBlock,
            _root_.MIPStarRE.QPBT.ProjectiveSetting.contentOfTuple] using hX.2.2
        · simp at hZ
  | Z =>
      simp only [_root_.MIPStarRE.QPBT.pauliPointVariableCondition] at hwin
      rcases hwin with hzero | hrest
      · exact (hgamma hzero).elim
      · rcases hrest with hX | hZ
        · simp at hX
        · simpa [_root_.MIPStarRE.QPBT.WinImplications.selectedTupleScalar, _root_.MIPStarRE.QPBT.WinImplications.pauliSharedSplit, _root_.MIPStarRE.QPBT.pauliRZBlock,
            _root_.MIPStarRE.QPBT.ProjectiveSetting.contentOfTuple] using hZ.2.2
