-- Prove2me | solution 1 for MIPStarRE.QPBT.WinImplications.pauliBasisConsistency_eq_mismatch
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T02:37:31.6548+00:00
-- url     : https://prove2.me/submissions/ef1f0114-ebab-496f-a3f7-0486f911300c

-- Generated proof for MIPStarRE.QPBT.WinImplications.pauliBasisConsistency_eq_mismatch.
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
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_LowDegree
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

theorem solution {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}
    (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) (W : _root_.MIPStarRE.QPBT.PauliKind) :
    _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P))
        (fun u a => _root_.MIPStarRE.QPBT.heteroKron ((S.pointMeas .alice W u).effect a) 1)
        (fun u a => _root_.MIPStarRE.QPBT.heteroKron 1 ((S.pauliEvalMeas .bob W u).effect a))
        S.toStrategy.ψ =
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P)) (fun u =>
        _root_.MIPStarRE.QPBT.outcomeEventWeight S.toStrategy
          (_root_.MIPStarRE.QPBT.ProjectiveSetting.pointQuestion P W u) (_root_.MIPStarRE.QPBT.pauliQuestion P W)
          (fun A B => _root_.MIPStarRE.QPBT.ProjectiveSetting.pointAnswerOrZero A ≠
            _root_.MIPStarRE.QPBT.lowDegreeEnc (_root_.MIPStarRE.QPBT.pauliAnswerOrZero B) u)) := by
  let X := Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P
  let qA : X → _root_.MIPStarRE.QPBT.PauliQuestion P := fun u => _root_.MIPStarRE.QPBT.ProjectiveSetting.pointQuestion P W u
  let qB : X → _root_.MIPStarRE.QPBT.PauliQuestion P := fun _ => _root_.MIPStarRE.QPBT.pauliQuestion P W
  let fA : X → _root_.MIPStarRE.QPBT.PauliAnswer P → _root_.MIPStarRE.QPBT.PauliScalar P := fun _ =>
    _root_.MIPStarRE.QPBT.ProjectiveSetting.pointAnswerOrZero
  let fB : X → _root_.MIPStarRE.QPBT.PauliAnswer P → _root_.MIPStarRE.QPBT.PauliScalar P := fun u B =>
    _root_.MIPStarRE.QPBT.lowDegreeEnc (_root_.MIPStarRE.QPBT.pauliAnswerOrZero B) u
  have h := _root_.MIPStarRE.QPBT.WinImplications.consistencyDefect_postprocess_eq_mismatch
    (X := X) (_root_.LIDT.MIPStarRE.LDT.uniformDistribution X) S.toStrategy qA qB fA fB
  have hA : ∀ (u : X) c,
      _root_.MIPStarRE.QPBT.heteroKron ((S.pointMeas .alice W u).effect c)
          (1 : _root_.LIDT.MIPStarRE.Quantum.Op S.toStrategy.ιB) =
        _root_.MIPStarRE.QPBT.heteroKron (((S.toStrategy.A (qA u)).postprocess (fA u)).effect c)
          (1 : _root_.LIDT.MIPStarRE.Quantum.Op S.toStrategy.ιB) := by
    intro u c
    rfl
  have hB : ∀ (u : X) c,
      _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op S.toStrategy.ιA) ((S.pauliEvalMeas .bob W u).effect c) =
        _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op S.toStrategy.ιA)
          (((S.toStrategy.B (qB u)).postprocess (fB u)).effect c) := by
    intro u c
    congr 1
    unfold _root_.MIPStarRE.QPBT.ProjectiveSetting.pauliEvalMeas _root_.MIPStarRE.QPBT.ProjectiveSetting.pauliMeas fB qB
    rw [_root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_comp]
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
