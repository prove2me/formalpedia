-- Prove2me | solution 1 for MIPStarRE.QPBT.WinImplications.lowDegreeConsistency_eq_mismatch
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T02:37:31.73009+00:00
-- url     : https://prove2.me/submissions/6e86f807-76ca-43e7-8015-864cf5ccae62

-- Generated proof for MIPStarRE.QPBT.WinImplications.lowDegreeConsistency_eq_mismatch.
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
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_LineDefs
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_LowDegree
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_Setup
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
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
    _root_.MIPStarRE.QPBT.consistencyDefect (_root_.MIPStarRE.QPBT.linePointDist P.toLdParams)
        (fun sample a => _root_.MIPStarRE.QPBT.heteroKron
          ((S.lineEvalMeas .alice W sample.1 sample.2).effect a) 1)
        (fun sample a => _root_.MIPStarRE.QPBT.heteroKron 1
          ((S.pointMeasOption .bob W sample.2).effect a))
        S.toStrategy.ψ =
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.linePointDist P.toLdParams) (fun sample =>
        _root_.MIPStarRE.QPBT.outcomeEventWeight S.toStrategy
          (_root_.MIPStarRE.QPBT.ProjectiveSetting.lineQuestion P W sample.1)
          (_root_.MIPStarRE.QPBT.ProjectiveSetting.pointQuestion P W sample.2)
          (fun A B =>
            _root_.MIPStarRE.QPBT.evalOpt sample.1 sample.2
                (_root_.MIPStarRE.QPBT.ProjectiveSetting.lineAnswerOrZero P sample.1 A) ≠
              some (_root_.MIPStarRE.QPBT.ProjectiveSetting.pointAnswerOrZero B))) := by
  let X := _root_.MIPStarRE.QPBT.LineDesc P.toLdParams × (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P)
  let qA : X → _root_.MIPStarRE.QPBT.PauliQuestion P := fun sample =>
    _root_.MIPStarRE.QPBT.ProjectiveSetting.lineQuestion P W sample.1
  let qB : X → _root_.MIPStarRE.QPBT.PauliQuestion P := fun sample =>
    _root_.MIPStarRE.QPBT.ProjectiveSetting.pointQuestion P W sample.2
  let fA : X → _root_.MIPStarRE.QPBT.PauliAnswer P → Option (_root_.MIPStarRE.QPBT.PauliScalar P) := fun sample A =>
    _root_.MIPStarRE.QPBT.evalOpt sample.1 sample.2 (_root_.MIPStarRE.QPBT.ProjectiveSetting.lineAnswerOrZero P sample.1 A)
  let fB : X → _root_.MIPStarRE.QPBT.PauliAnswer P → Option (_root_.MIPStarRE.QPBT.PauliScalar P) := fun _ B =>
    some (_root_.MIPStarRE.QPBT.ProjectiveSetting.pointAnswerOrZero B)
  have h := _root_.MIPStarRE.QPBT.WinImplications.consistencyDefect_postprocess_eq_mismatch
    (X := X) (_root_.MIPStarRE.QPBT.linePointDist P.toLdParams) S.toStrategy qA qB fA fB
  have hA : ∀ (sample : X) c,
      _root_.MIPStarRE.QPBT.heteroKron ((S.lineEvalMeas .alice W sample.1 sample.2).effect c)
          (1 : _root_.LIDT.MIPStarRE.Quantum.Op S.toStrategy.ιB) =
        _root_.MIPStarRE.QPBT.heteroKron
          (((S.toStrategy.A (qA sample)).postprocess (fA sample)).effect c)
          (1 : _root_.LIDT.MIPStarRE.Quantum.Op S.toStrategy.ιB) := by
    intro sample c
    congr 1
    unfold _root_.MIPStarRE.QPBT.ProjectiveSetting.lineEvalMeas _root_.MIPStarRE.QPBT.ProjectiveSetting.lineMeas qA fA
    rw [_root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_comp]
    rfl
  have hB : ∀ (sample : X) c,
      _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op S.toStrategy.ιA)
          ((S.pointMeasOption .bob W sample.2).effect c) =
        _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op S.toStrategy.ιA)
          (((S.toStrategy.B (qB sample)).postprocess (fB sample)).effect c) := by
    intro sample c
    congr 1
    unfold _root_.MIPStarRE.QPBT.ProjectiveSetting.pointMeasOption _root_.MIPStarRE.QPBT.ProjectiveSetting.pointMeas qB fB
    rw [_root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_comp]
    rfl
  calc
    _root_.MIPStarRE.QPBT.consistencyDefect (_root_.MIPStarRE.QPBT.linePointDist P.toLdParams)
        (fun sample a => _root_.MIPStarRE.QPBT.heteroKron
          ((S.lineEvalMeas .alice W sample.1 sample.2).effect a) 1)
        (fun sample a => _root_.MIPStarRE.QPBT.heteroKron 1
          ((S.pointMeasOption .bob W sample.2).effect a))
        S.toStrategy.ψ =
        _root_.MIPStarRE.QPBT.consistencyDefect (_root_.MIPStarRE.QPBT.linePointDist P.toLdParams)
          (fun sample c => _root_.MIPStarRE.QPBT.heteroKron
            (((S.toStrategy.A (qA sample)).postprocess (fA sample)).effect c) 1)
          (fun sample c => _root_.MIPStarRE.QPBT.heteroKron 1
            (((S.toStrategy.B (qB sample)).postprocess (fB sample)).effect c))
          S.toStrategy.ψ := _root_.MIPStarRE.QPBT.consistencyDefect_congr _ _ _ _ _ _ hA hB
    _ = _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.linePointDist P.toLdParams) (fun sample =>
        _root_.MIPStarRE.QPBT.outcomeEventWeight S.toStrategy (qA sample) (qB sample)
          (fun A B => fA sample A ≠ fB sample B)) := h
    _ = _ := by rfl
