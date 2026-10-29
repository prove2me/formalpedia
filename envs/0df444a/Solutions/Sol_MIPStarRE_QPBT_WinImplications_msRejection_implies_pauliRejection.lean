-- Prove2me | solution 1 for MIPStarRE.QPBT.WinImplications.msRejection_implies_pauliRejection
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T00:45:52.023502+00:00
-- url     : https://prove2.me/submissions/2f0008da-ea37-4a8d-aabc-aa73f385bc93

-- Generated proof for MIPStarRE.QPBT.WinImplications.msRejection_implies_pauliRejection.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
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
import Definitions.Def_QPBT_QPBT_Games_CondLinear
import Definitions.Def_QPBT_QPBT_Observables_Anticommuting
import Definitions.Def_QPBT_QPBT_Observables_Defs
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

theorem solution
    (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (z : _root_.MIPStarRE.QPBT.PauliSpace P) (xy : _root_.MIPStarRE.QPBT.MsType × _root_.MIPStarRE.QPBT.MsType)
    (hxy : xy ∈ (_root_.MIPStarRE.QPBT.graphDistribution _root_.MIPStarRE.QPBT.msEdges _root_.MIPStarRE.QPBT.msEdges_nonempty).support)
    (hanti : _root_.MIPStarRE.QPBT.IsAnticommuting (_root_.MIPStarRE.QPBT.WinImplications.pauliSharedSplit P z).1)
    (A B : _root_.MIPStarRE.QPBT.PauliAnswer P)
    (hreject : _root_.MIPStarRE.QPBT.msWinPredicate xy.1 xy.2
      (_root_.MIPStarRE.QPBT.ProjectiveSetting.msAnswerOrZero xy.1 A)
      (_root_.MIPStarRE.QPBT.ProjectiveSetting.msAnswerOrZero xy.2 B) = false) :
    _root_.MIPStarRE.QPBT.pauliWinPredicate P
      ((.ms xy.1), _root_.MIPStarRE.QPBT.pauliCL P (.ms xy.1) z)
      ((.ms xy.2), _root_.MIPStarRE.QPBT.pauliCL P (.ms xy.2) z) A B = false := by
  have hedge : Sym2.mk xy.1 xy.2 ∈ _root_.MIPStarRE.QPBT.msEdges :=
    (Finset.mem_filter.mp hxy).2
  rcases Finset.mem_image.mp hedge with ⟨ik, _, heq⟩
  have hor :
      ((.constraint ik.1, .var (_root_.MIPStarRE.QPBT.msConstraintVars ik.1 ik.2)) :
          _root_.MIPStarRE.QPBT.MsType × _root_.MIPStarRE.QPBT.MsType) = xy ∨
        ((.constraint ik.1, .var (_root_.MIPStarRE.QPBT.msConstraintVars ik.1 ik.2)) :
          _root_.MIPStarRE.QPBT.MsType × _root_.MIPStarRE.QPBT.MsType) = xy.swap :=
    (Sym2.mk_eq_mk_iff (α := _root_.MIPStarRE.QPBT.MsType)).mp heq
  have hgamma (t : _root_.MIPStarRE.QPBT.MsType) : _root_.MIPStarRE.QPBT.pauliPairGamma P (_root_.MIPStarRE.QPBT.pauliCL P (.ms t) z) ≠ 0 := by
    change _root_.MIPStarRE.QPBT.gammaValue P (_root_.MIPStarRE.QPBT.pauliXBlock z) (_root_.MIPStarRE.QPBT.pauliZBlock z)
      (_root_.MIPStarRE.QPBT.pauliRXBlock z) (_root_.MIPStarRE.QPBT.pauliRZBlock z) ≠ 0 at hanti
    rw [_root_.MIPStarRE.QPBT.WinImplications.pauliCL_shared_eq P (.ms t) rfl]
    change _root_.MIPStarRE.QPBT.gammaValue P (_root_.MIPStarRE.QPBT.pauliXBlock z) (_root_.MIPStarRE.QPBT.pauliZBlock z)
      (_root_.MIPStarRE.QPBT.pauliRXBlock z) (_root_.MIPStarRE.QPBT.pauliRZBlock z) ≠ 0
    exact hanti
  rcases hor with hforward | hreverse
  · subst xy
    cases A <;> cases B <;>
      simp_all only [Finset.mem_univ, ne_eq, _root_.MIPStarRE.QPBT.ProjectiveSetting.msAnswerOrZero,
        _root_.MIPStarRE.QPBT.pauliWinPredicate, _root_.MIPStarRE.QPBT.validPauliAnswer, Bool.and_self, Bool.and_true,
        Bool.and_false, Bool.false_eq_true, ↓reduceIte, _root_.MIPStarRE.QPBT.PauliType.ms.injEq,
        reduceCtorEq, exists_apply_eq_apply, or_self, decide_false]
  · have hswap := congrArg Prod.swap hreverse
    have hxy : xy =
        ((.var (_root_.MIPStarRE.QPBT.msConstraintVars ik.1 ik.2), .constraint ik.1) :
          _root_.MIPStarRE.QPBT.MsType × _root_.MIPStarRE.QPBT.MsType) := by
      simpa using hswap.symm
    subst xy
    clear hreverse hswap hedge heq
    cases A <;> cases B <;>
      simp_all only [Finset.mem_univ, ne_eq, _root_.MIPStarRE.QPBT.ProjectiveSetting.msAnswerOrZero,
        _root_.MIPStarRE.QPBT.pauliWinPredicate, _root_.MIPStarRE.QPBT.validPauliAnswer, Bool.and_self, Bool.and_true,
        Bool.and_false, Bool.false_eq_true, ↓reduceIte, _root_.MIPStarRE.QPBT.PauliType.ms.injEq,
        reduceCtorEq, exists_apply_eq_apply, or_self, decide_false]
