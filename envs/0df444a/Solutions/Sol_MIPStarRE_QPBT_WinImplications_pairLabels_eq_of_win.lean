-- Prove2me | solution 1 for MIPStarRE.QPBT.WinImplications.pairLabels_eq_of_win
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T00:12:24.294146+00:00
-- url     : https://prove2.me/submissions/7e4910c0-01d7-4814-bb53-60daac1a98e4

-- Generated proof for MIPStarRE.QPBT.WinImplications.pairLabels_eq_of_win.
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
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Observables_Anticommuting
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_Commuting
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_LowDegree
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
# Commuting winning implications

This module proves the exact Pair/W and point-trace consistency bounds on
commuting Pauli tuples.

## References

The commuting-tuple consistency theorems prove items 4 and 5
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
    (hcomm : _root_.MIPStarRE.QPBT.IsCommuting (_root_.MIPStarRE.QPBT.WinImplications.pauliSharedSplit P z).1)
    (hwin : _root_.MIPStarRE.QPBT.pauliWinPredicate P
      ((.pairW W), _root_.MIPStarRE.QPBT.pauliCL P (.pairW W) z)
      (.pair, _root_.MIPStarRE.QPBT.pauliCL P .pair z) A B = true) :
    _root_.MIPStarRE.QPBT.ProjectiveSetting.pairWAnswerOrZero A =
      _root_.MIPStarRE.QPBT.WinImplications.selectedPairBit W (_root_.MIPStarRE.QPBT.ProjectiveSetting.pairAnswerOrZero B) := by
  cases A <;> cases B <;>
    simp only [_root_.MIPStarRE.QPBT.pauliWinPredicate, _root_.MIPStarRE.QPBT.validPauliAnswer, Bool.and_true,
      Bool.and_self, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
      reduceCtorEq, decide_eq_true_eq] at hwin
  rename_i bit bits
  simp only [_root_.MIPStarRE.QPBT.ProjectiveSetting.pairWAnswerOrZero,
    _root_.MIPStarRE.QPBT.ProjectiveSetting.pairAnswerOrZero]
  have hgamma : _root_.MIPStarRE.QPBT.pauliPairGamma P (_root_.MIPStarRE.QPBT.pauliCL P (.pairW W) z) = 0 := by
    change _root_.MIPStarRE.QPBT.gammaValue P (_root_.MIPStarRE.QPBT.pauliXBlock z) (_root_.MIPStarRE.QPBT.pauliZBlock z)
      (_root_.MIPStarRE.QPBT.pauliRXBlock z) (_root_.MIPStarRE.QPBT.pauliRZBlock z) = 0 at hcomm
    rw [_root_.MIPStarRE.QPBT.WinImplications.pauliCL_shared_eq P (.pairW W) rfl]
    change _root_.MIPStarRE.QPBT.gammaValue P (_root_.MIPStarRE.QPBT.pauliXBlock z) (_root_.MIPStarRE.QPBT.pauliZBlock z)
      (_root_.MIPStarRE.QPBT.pauliRXBlock z) (_root_.MIPStarRE.QPBT.pauliRZBlock z) = 0
    exact hcomm
  cases W <;>
    simp only [_root_.MIPStarRE.QPBT.pauliPairCondition, hgamma, ne_eq, not_true_eq_false,
      false_or, _root_.MIPStarRE.QPBT.WinImplications.selectedPairBit] at hwin ⊢ <;>
    exact hwin.symm
