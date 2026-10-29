-- Prove2me | solution 1 for MIPStarRE.QPBT.WinImplications.msConsConsistency_eq_mismatch_interchanged
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T02:18:01.376179+00:00
-- url     : https://prove2.me/submissions/67471bf1-108c-447b-aadb-9e33e95d059b

-- Generated proof for MIPStarRE.QPBT.WinImplications.msConsConsistency_eq_mismatch_interchanged.
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
import Definitions.Def_QPBT_QPBT_Observables_Anticommuting
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_Approx
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_Commuting
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_MagicSquare
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_Setup
import Definitions.Def_QPBT_QPBT_Test_MagicSquare
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
    {ε : ℝ} (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) (W : _root_.MIPStarRE.QPBT.PauliKind) :
    _root_.MIPStarRE.QPBT.consistencyDefect (_root_.MIPStarRE.QPBT.anticommTupleDist P)
        (fun ω a => _root_.MIPStarRE.QPBT.heteroKron
          ((S.msVarBitMeas .alice (_root_.MIPStarRE.QPBT.WinImplications.selectedMsVar W) ω).effect a) 1)
        (fun ω a => _root_.MIPStarRE.QPBT.heteroKron 1
          ((S.pointTraceMeas .bob W (_root_.MIPStarRE.QPBT.WinImplications.selectedTuplePoint W ω)
            (_root_.MIPStarRE.QPBT.WinImplications.selectedTupleScalar W ω)).effect a))
        S.toStrategy.ψ =
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.anticommTupleDist P) (fun ω =>
        _root_.MIPStarRE.QPBT.outcomeEventWeight S.toStrategy
          (_root_.MIPStarRE.QPBT.ProjectiveSetting.msQuestion P (.var (_root_.MIPStarRE.QPBT.WinImplications.selectedMsVar W))
            ω.1 ω.2.1 ω.2.2.1 ω.2.2.2)
          (_root_.MIPStarRE.QPBT.ProjectiveSetting.pointQuestion P W (_root_.MIPStarRE.QPBT.WinImplications.selectedTuplePoint W ω))
          (fun A B => _root_.MIPStarRE.QPBT.ProjectiveSetting.pairWAnswerOrZero A ≠
            _root_.MIPStarRE.QPBT.WinImplications.pointTraceLabel P W ω B)) := by
  let qA : _root_.MIPStarRE.QPBT.PauliTuple P → _root_.MIPStarRE.QPBT.PauliQuestion P := fun ω =>
    _root_.MIPStarRE.QPBT.ProjectiveSetting.msQuestion P (.var (_root_.MIPStarRE.QPBT.WinImplications.selectedMsVar W))
      ω.1 ω.2.1 ω.2.2.1 ω.2.2.2
  let qB : _root_.MIPStarRE.QPBT.PauliTuple P → _root_.MIPStarRE.QPBT.PauliQuestion P := fun ω =>
    _root_.MIPStarRE.QPBT.ProjectiveSetting.pointQuestion P W (_root_.MIPStarRE.QPBT.WinImplications.selectedTuplePoint W ω)
  let fA : _root_.MIPStarRE.QPBT.PauliTuple P → _root_.MIPStarRE.QPBT.PauliAnswer P → ZMod 2 := fun _ =>
    _root_.MIPStarRE.QPBT.ProjectiveSetting.pairWAnswerOrZero
  let fB : _root_.MIPStarRE.QPBT.PauliTuple P → _root_.MIPStarRE.QPBT.PauliAnswer P → ZMod 2 := fun ω B =>
    _root_.MIPStarRE.QPBT.WinImplications.pointTraceLabel P W ω B
  have h := _root_.MIPStarRE.QPBT.WinImplications.consistencyDefect_postprocess_eq_mismatch
    (_root_.MIPStarRE.QPBT.anticommTupleDist P) S.toStrategy qA qB fA fB
  have hA : ∀ ω c,
      _root_.MIPStarRE.QPBT.heteroKron ((S.msVarBitMeas .alice (_root_.MIPStarRE.QPBT.WinImplications.selectedMsVar W) ω).effect c)
          (1 : _root_.LIDT.MIPStarRE.Quantum.Op S.toStrategy.ιB) =
        _root_.MIPStarRE.QPBT.heteroKron (((S.toStrategy.A (qA ω)).postprocess (fA ω)).effect c)
          (1 : _root_.LIDT.MIPStarRE.Quantum.Op S.toStrategy.ιB) := by
    intro ω c
    congr 1
    unfold _root_.MIPStarRE.QPBT.ProjectiveSetting.msVarBitMeas _root_.MIPStarRE.QPBT.ProjectiveSetting.msMeas fA qA
    rw [_root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_comp]
    have hmap : (_root_.MIPStarRE.QPBT.msBitOrZero ∘
        _root_.MIPStarRE.QPBT.ProjectiveSetting.msAnswerOrZero (P := P) (.var (_root_.MIPStarRE.QPBT.WinImplications.selectedMsVar W))) =
        _root_.MIPStarRE.QPBT.ProjectiveSetting.pairWAnswerOrZero (P := P) := by
      funext B
      cases B <;> rfl
    rw [Function.comp_def] at hmap
    rw [hmap]
    rfl
  have hB : ∀ ω c,
      _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op S.toStrategy.ιA)
          ((S.pointTraceMeas .bob W (_root_.MIPStarRE.QPBT.WinImplications.selectedTuplePoint W ω)
            (_root_.MIPStarRE.QPBT.WinImplications.selectedTupleScalar W ω)).effect c) =
        _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op S.toStrategy.ιA)
          (((S.toStrategy.B (qB ω)).postprocess (fB ω)).effect c) := by
    intro ω c
    congr 1
    unfold _root_.MIPStarRE.QPBT.ProjectiveSetting.pointTraceMeas _root_.MIPStarRE.QPBT.ProjectiveSetting.pointMeas fB
    rw [_root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_comp]
    rfl
  calc
    _ = _root_.MIPStarRE.QPBT.consistencyDefect (_root_.MIPStarRE.QPBT.anticommTupleDist P)
        (fun ω c => _root_.MIPStarRE.QPBT.heteroKron
          (((S.toStrategy.A (qA ω)).postprocess (fA ω)).effect c) 1)
        (fun ω c => _root_.MIPStarRE.QPBT.heteroKron 1
          (((S.toStrategy.B (qB ω)).postprocess (fB ω)).effect c))
        S.toStrategy.ψ := _root_.MIPStarRE.QPBT.consistencyDefect_congr _ _ _ _ _ _ hA hB
    _ = _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.anticommTupleDist P) (fun ω =>
        _root_.MIPStarRE.QPBT.outcomeEventWeight S.toStrategy (qA ω) (qB ω)
          (fun A B => fA ω A ≠ fB ω B)) := h
    _ = _ := by rfl
