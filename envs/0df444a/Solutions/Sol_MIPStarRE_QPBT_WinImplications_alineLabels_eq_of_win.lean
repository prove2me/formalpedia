-- Prove2me | solution 1 for MIPStarRE.QPBT.WinImplications.alineLabels_eq_of_win
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T00:37:05.688999+00:00
-- url     : https://prove2.me/submissions/923fced5-6d0a-49c0-a89e-fe6db2894201

-- Generated proof for MIPStarRE.QPBT.WinImplications.alineLabels_eq_of_win.
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
import Theorems.Thm_MIPStarRE_QPBT_WinImplications_aline_winning_condition
import Theorems.Thm_MIPStarRE_QPBT_WinImplications_evalCoefficient_padTo

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





































/-- A uniquely determined line evaluation is returned by `evalOpt`. -/
theorem evalOpt_eq_some_of_evaluatesTo {L : _root_.MIPStarRE.QPBT.LdParams} {c : ℕ}
    (line : _root_.MIPStarRE.QPBT.LineDesc L) (f : _root_.MIPStarRE.QPBT.DegPoly L c) (u : Fin L.m → _root_.MIPStarRE.QPBT.ScalarQ L)
    (a : _root_.MIPStarRE.QPBT.ScalarQ L) (h : _root_.MIPStarRE.QPBT.EvaluatesTo line f u a) :
    _root_.MIPStarRE.QPBT.evalOpt line u f = some a := by
  unfold _root_.MIPStarRE.QPBT.evalOpt
  rw [dif_pos ⟨a, h⟩]
  apply congrArg some
  obtain ⟨t, ht⟩ := h.1
  exact ((Classical.choose_spec ⟨a, h⟩).2 t ht).symm.trans (h.2 t ht)

/-- The sampled point lies on its canonical axis line. -/
theorem point_mem_sampled_aline (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (W : _root_.MIPStarRE.QPBT.PauliKind)
    (z : _root_.MIPStarRE.QPBT.PauliSpace P) :
    (_root_.MIPStarRE.QPBT.pauliToLd P W z).point ∈
      (_root_.MIPStarRE.QPBT.aLineDescOf P.toLdParams
        (_root_.MIPStarRE.QPBT.ldALineCL P.toLdParams (_root_.MIPStarRE.QPBT.pauliToLd P W z))).pointSet := by
  change (_root_.MIPStarRE.QPBT.pauliToLd P W z).point ∈ _root_.MIPStarRE.QPBT.linePoints
    (_root_.MIPStarRE.QPBT.lineRepMap
      (_root_.MIPStarRE.QPBT.coordinateDirection (_root_.MIPStarRE.QPBT.chiIndex P.toLdParams (_root_.MIPStarRE.QPBT.pauliToLd P W z).seed))
      (_root_.MIPStarRE.QPBT.lineRepMap
        (_root_.MIPStarRE.QPBT.coordinateDirection (_root_.MIPStarRE.QPBT.chiIndex P.toLdParams (_root_.MIPStarRE.QPBT.pauliToLd P W z).seed))
        (_root_.MIPStarRE.QPBT.pauliToLd P W z).point))
    (_root_.MIPStarRE.QPBT.coordinateDirection (_root_.MIPStarRE.QPBT.chiIndex P.toLdParams (_root_.MIPStarRE.QPBT.pauliToLd P W z).seed))
  rw [_root_.MIPStarRE.QPBT.lineRepMap_apply_self]
  exact _root_.MIPStarRE.QPBT.mem_linePoints_lineRepMap _ _






















































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
    (z : _root_.MIPStarRE.QPBT.PauliSpace P) (A B : _root_.MIPStarRE.QPBT.PauliAnswer P)
    (hwin : _root_.MIPStarRE.QPBT.pauliWinPredicate P
      ((.aline W), _root_.MIPStarRE.QPBT.pauliCL P (.aline W) z)
      ((.point W), _root_.MIPStarRE.QPBT.pauliCL P (.point W) z) A B = true) :
    _root_.MIPStarRE.QPBT.evalOpt
        (_root_.MIPStarRE.QPBT.aLineDescOf P.toLdParams (_root_.MIPStarRE.QPBT.ldALineCL P.toLdParams (_root_.MIPStarRE.QPBT.pauliToLd P W z)))
        (_root_.MIPStarRE.QPBT.pauliToLd P W z).point
        (_root_.MIPStarRE.QPBT.ProjectiveSetting.lineAnswerOrZero P
          (_root_.MIPStarRE.QPBT.aLineDescOf P.toLdParams (_root_.MIPStarRE.QPBT.ldALineCL P.toLdParams (_root_.MIPStarRE.QPBT.pauliToLd P W z))) A) =
      some (_root_.MIPStarRE.QPBT.ProjectiveSetting.pointAnswerOrZero B) := by
  cases A <;> cases B <;>
    simp only [_root_.MIPStarRE.QPBT.pauliWinPredicate, _root_.MIPStarRE.QPBT.validPauliAnswer, Bool.and_true,
      Bool.and_self, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
      reduceCtorEq, decide_eq_true_eq] at hwin
  rename_i f a
  apply _root_.MIPStarRE.QPBT.WinImplications.evalOpt_eq_some_of_evaluatesTo
  refine ⟨_root_.MIPStarRE.QPBT.WinImplications.point_mem_sampled_aline P W z, ?_⟩
  intro t ht
  let hpad : P.d ≤ P.m * P.d :=
    Nat.le_mul_of_pos_left P.d (Nat.zero_lt_of_lt P.one_le_m)
  rw [show _root_.MIPStarRE.QPBT.ProjectiveSetting.lineAnswerOrZero P
      (_root_.MIPStarRE.QPBT.aLineDescOf P.toLdParams (_root_.MIPStarRE.QPBT.ldALineCL P.toLdParams (_root_.MIPStarRE.QPBT.pauliToLd P W z)))
      (.alinePoly f) = _root_.MIPStarRE.QPBT.DegPoly.padTo hpad f by rfl]
  rw [_root_.MIPStarRE.QPBT.WinImplications.evalCoefficient_padTo hpad]
  change _root_.MIPStarRE.QPBT.evalCoefficient f t = a
  exact _root_.MIPStarRE.QPBT.WinImplications.aline_winning_condition P W z f a (by
    simpa [_root_.MIPStarRE.QPBT.pauliWinPredicate, _root_.MIPStarRE.QPBT.validPauliAnswer] using hwin) t ht
