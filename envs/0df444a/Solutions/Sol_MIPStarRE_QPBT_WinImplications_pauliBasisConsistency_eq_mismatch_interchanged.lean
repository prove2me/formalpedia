-- Prove2me | solution 1 for MIPStarRE.QPBT.WinImplications.pauliBasisConsistency_eq_mismatch_interchanged
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T02:22:38.995954+00:00
-- url     : https://prove2.me/submissions/e3b2b752-0bf2-4335-bb0d-359d3363e542

-- Generated proof for MIPStarRE.QPBT.WinImplications.pauliBasisConsistency_eq_mismatch_interchanged.
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
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_LowDegreeCode
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_ApproxLines
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_Setup
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Theorems.Thm_LIDT_MIPStarRE_Quantum_Measurement_postprocess_comp
import Theorems.Thm_MIPStarRE_QPBT_WinImplications_consistencyDefect_postprocess_eq_mismatch
import Theorems.Thm_MIPStarRE_QPBT_consistencyDefect_congr

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.WinImplications
end MIPStarRE.QPBT.WinImplications

/-!
# Approximate winning implications for the line and point subtests

This module proves the operator-distance companions, with their
factor-interchanged forms, of the consistency check, the low-degree check,
and the Pauli basis consistency check.

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



/-! ## Consistency check -/



/-! ## Low-degree check -/



















/-! ## Pauli basis consistency check -/
attribute [local instance] _root_.MIPStarRE.QPBT.WinImplications.pauliEdgeNonemptyApproxLines

theorem solution {P : _root_.MIPStarRE.QPBT.AdmissibleParams}
    {ε : ℝ} (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) (W : _root_.MIPStarRE.QPBT.PauliKind) :
    _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P))
        (fun u a => _root_.MIPStarRE.QPBT.heteroKron ((S.pauliEvalMeas .alice W u).effect a) 1)
        (fun u a => _root_.MIPStarRE.QPBT.heteroKron 1 ((S.pointMeas .bob W u).effect a))
        S.toStrategy.ψ =
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P)) (fun u =>
        _root_.MIPStarRE.QPBT.outcomeEventWeight S.toStrategy
          (_root_.MIPStarRE.QPBT.pauliQuestion P W) (_root_.MIPStarRE.QPBT.ProjectiveSetting.pointQuestion P W u)
          (fun A B => _root_.MIPStarRE.QPBT.lowDegreeEnc (_root_.MIPStarRE.QPBT.pauliAnswerOrZero A) u ≠
            _root_.MIPStarRE.QPBT.ProjectiveSetting.pointAnswerOrZero B)) := by
  let X := Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P
  let qA : X → _root_.MIPStarRE.QPBT.PauliQuestion P := fun _ => _root_.MIPStarRE.QPBT.pauliQuestion P W
  let qB : X → _root_.MIPStarRE.QPBT.PauliQuestion P := fun u => _root_.MIPStarRE.QPBT.ProjectiveSetting.pointQuestion P W u
  let fA : X → _root_.MIPStarRE.QPBT.PauliAnswer P → _root_.MIPStarRE.QPBT.PauliScalar P := fun u A =>
    _root_.MIPStarRE.QPBT.lowDegreeEnc (_root_.MIPStarRE.QPBT.pauliAnswerOrZero A) u
  let fB : X → _root_.MIPStarRE.QPBT.PauliAnswer P → _root_.MIPStarRE.QPBT.PauliScalar P := fun _ =>
    _root_.MIPStarRE.QPBT.ProjectiveSetting.pointAnswerOrZero
  have h := _root_.MIPStarRE.QPBT.WinImplications.consistencyDefect_postprocess_eq_mismatch
    (X := X) (_root_.LIDT.MIPStarRE.LDT.uniformDistribution X) S.toStrategy qA qB fA fB
  have hA : ∀ (u : X) c,
      _root_.MIPStarRE.QPBT.heteroKron ((S.pauliEvalMeas .alice W u).effect c)
          (1 : _root_.LIDT.MIPStarRE.Quantum.Op S.toStrategy.ιB) =
        _root_.MIPStarRE.QPBT.heteroKron (((S.toStrategy.A (qA u)).postprocess (fA u)).effect c)
          (1 : _root_.LIDT.MIPStarRE.Quantum.Op S.toStrategy.ιB) := by
    intro u c
    congr 1
    unfold _root_.MIPStarRE.QPBT.ProjectiveSetting.pauliEvalMeas _root_.MIPStarRE.QPBT.ProjectiveSetting.pauliMeas fA qA
    rw [_root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_comp]
    rfl
  have hB : ∀ (u : X) c,
      _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op S.toStrategy.ιA) ((S.pointMeas .bob W u).effect c) =
        _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op S.toStrategy.ιA)
          (((S.toStrategy.B (qB u)).postprocess (fB u)).effect c) := by
    intro u c
    rfl
  calc
    _ = _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution X)
        (fun u c => _root_.MIPStarRE.QPBT.heteroKron
          (((S.toStrategy.A (qA u)).postprocess (fA u)).effect c) 1)
        (fun u c => _root_.MIPStarRE.QPBT.heteroKron 1
          (((S.toStrategy.B (qB u)).postprocess (fB u)).effect c))
        S.toStrategy.ψ := _root_.MIPStarRE.QPBT.consistencyDefect_congr _ _ _ _ _ _ hA hB
    _ = _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution X) (fun u =>
        _root_.MIPStarRE.QPBT.outcomeEventWeight S.toStrategy (qA u) (qB u)
          (fun A B => fA u A ≠ fB u B)) := h
    _ = _ := by rfl
