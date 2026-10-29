-- Prove2me | solution 1 for MIPStarRE.QPBT.WinImplications.pointMsMismatch_le_rejection_interchanged
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T00:45:51.782098+00:00
-- url     : https://prove2.me/submissions/4cac61cf-37ac-48cf-96a7-e81d01475f50

-- Generated proof for MIPStarRE.QPBT.WinImplications.pointMsMismatch_le_rejection_interchanged.
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
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Observables_Anticommuting
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_Approx
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_Averages
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_Commuting
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_Interchange
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_LowDegree
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_MagicSquare
import Definitions.Def_QPBT_QPBT_Test_MagicSquare
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Theorems.Thm_MIPStarRE_QPBT_WinImplications_pointMsLabels_eq_of_win
import Theorems.Thm_MIPStarRE_QPBT_outcome_event_weight_mono

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.WinImplications
end MIPStarRE.QPBT.WinImplications

/- Source helpers from QPBT/Observables/WinImplications/Interchange.lean. -/
/-!
# Interchange of the tensor factors in the winning implications

This module collects the statements shared by the operator-distance companions
of the winning implications and by their factor-interchanged forms: transport of
the state-dependent distance along the interchange of the two tensor factors,
the constant-factor passage from consistency to distance, the reversed
verifier edges, and the clause-by-clause symmetry of the Pauli win predicate
on the ordered type pairs that the implications use.

## References

The declarations support the trailing clause of `lem:qld-win-implications` in
`blueprint/src/chapter/ch14_qpbt_observables.tex:616-706`. Their paper source
is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:192-267`,
whose closing sentences at lines 227 and 263-264 state both companions.
-/

@[expose] public section

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

namespace WinImplications

/-! ## Transport of the distance functional along the factor interchange -/

















/-! ## Reversed verifier edges

The Pauli type graph is a set of unordered pairs, so every ordered edge used by
the exact implications has its reverse in the graph. The reversed edges carry
the interchanged conclusions of `lem:qld-win-implications`, blueprint
`ch14_qpbt_observables.tex:701-703`. -/













/-! ## Symmetry of the win predicate on the subtests used here

`def:pauli-win-predicate` lists every clause together with its mirror image, so
on each ordered type pair occurring in `lem:qld-win-implications` exchanging the
two questions and the two answers leaves the predicate unchanged. Paper
`08_classical_and_quantum_low_degree_tests.tex:1126-1225`, blueprint
`ch13_qpbt_test.tex:410-449`. -/











/-- Variable/point clause symmetry. -/
theorem win_symm_msvar_point (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (W : _root_.MIPStarRE.QPBT.PauliKind)
    (j : Fin 9) (x y : _root_.MIPStarRE.QPBT.PauliSpace P) (A B : _root_.MIPStarRE.QPBT.PauliAnswer P) :
    _root_.MIPStarRE.QPBT.pauliWinPredicate P (.ms (.var j), x) (.point W, y) A B =
      _root_.MIPStarRE.QPBT.pauliWinPredicate P (.point W, y) (.ms (.var j), x) B A := by
  cases A <;> cases B <;>
    simp [_root_.MIPStarRE.QPBT.pauliWinPredicate, _root_.MIPStarRE.QPBT.validPauliAnswer, eq_comm]

/-! ## Numeric bookkeeping -/





end WinImplications

end

end MIPStarRE.QPBT

/-!
# Approximate winning implications for the tuple subtests

This module proves the operator-distance companions, with their
factor-interchanged forms, of the commutation check, the commutation
consistency check, and the Magic Square consistency check.

## References

The declarations support the trailing clause of `lem:qld-win-implications` in
`blueprint/src/chapter/ch14_qpbt_observables.tex:614-702`. Their paper source
is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:192-267`,
whose closing sentences at lines 227 and 263-264 state both companions.
-/



open scoped BigOperators Matrix ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum



open MIPStarRE.QPBT.WinImplications



/-! ## Commutation check -/











/-! ## Commutation consistency check -/











/-! ## Magic square consistency check -/
attribute [local instance] _root_.MIPStarRE.QPBT.WinImplications.pauliEdgeNonemptyApprox

theorem solution {P : _root_.MIPStarRE.QPBT.AdmissibleParams}
    {ε : ℝ} (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) (W : _root_.MIPStarRE.QPBT.PauliKind) (z : _root_.MIPStarRE.QPBT.PauliSpace P)
    (hanti : _root_.MIPStarRE.QPBT.IsAnticommuting (_root_.MIPStarRE.QPBT.WinImplications.pauliSharedSplit P z).1) :
    _root_.MIPStarRE.QPBT.outcomeEventWeight S.toStrategy
        ((.ms (.var (_root_.MIPStarRE.QPBT.WinImplications.selectedMsVar W))),
          _root_.MIPStarRE.QPBT.pauliCL P (.ms (.var (_root_.MIPStarRE.QPBT.WinImplications.selectedMsVar W))) z)
        ((.point W), _root_.MIPStarRE.QPBT.pauliCL P (.point W) z)
        (fun A B => _root_.MIPStarRE.QPBT.ProjectiveSetting.pairWAnswerOrZero A ≠
          _root_.MIPStarRE.QPBT.WinImplications.pointTraceLabel P W (_root_.MIPStarRE.QPBT.WinImplications.pauliSharedSplit P z).1 B) ≤
      _root_.MIPStarRE.QPBT.WinImplications.pauliRejectionAt S.toStrategy (_root_.MIPStarRE.QPBT.WinImplications.msVarPointEdge W) z := by
  cases W with
  | X =>
      apply _root_.MIPStarRE.QPBT.outcome_event_weight_mono
      intro A B hne
      change _root_.MIPStarRE.QPBT.pauliWinPredicate P _ _ A B = false
      apply Bool.eq_false_iff.mpr
      intro htrue
      exact hne (_root_.MIPStarRE.QPBT.WinImplications.pointMsLabels_eq_of_win P .X z B A hanti
        ((_root_.MIPStarRE.QPBT.WinImplications.win_symm_msvar_point P .X (_root_.MIPStarRE.QPBT.WinImplications.selectedMsVar .X) _ _ A B).symm.trans
          htrue)).symm
  | Z =>
      apply _root_.MIPStarRE.QPBT.outcome_event_weight_mono
      intro A B hne
      change _root_.MIPStarRE.QPBT.pauliWinPredicate P _ _ A B = false
      apply Bool.eq_false_iff.mpr
      intro htrue
      exact hne (_root_.MIPStarRE.QPBT.WinImplications.pointMsLabels_eq_of_win P .Z z B A hanti
        ((_root_.MIPStarRE.QPBT.WinImplications.win_symm_msvar_point P .Z (_root_.MIPStarRE.QPBT.WinImplications.selectedMsVar .Z) _ _ A B).symm.trans
          htrue)).symm
