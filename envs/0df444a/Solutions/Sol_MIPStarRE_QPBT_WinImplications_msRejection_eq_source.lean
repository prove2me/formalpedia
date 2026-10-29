-- Prove2me | solution 1 for MIPStarRE.QPBT.WinImplications.msRejection_eq_source
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T00:45:51.571105+00:00
-- url     : https://prove2.me/submissions/1de071fb-70d0-47e3-b8cb-2c6521bd8739

-- Generated proof for MIPStarRE.QPBT.WinImplications.msRejection_eq_source.
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
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Observables_Anticommuting
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_Setup
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

theorem solution {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}
    (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) (ω : _root_.MIPStarRE.QPBT.PauliTuple P) (x y : _root_.MIPStarRE.QPBT.MsType) :
    _root_.MIPStarRE.QPBT.outcomeEventWeight (S.msStrategyAt ω) x y
        (fun a b => _root_.MIPStarRE.QPBT.msWinPredicate x y a b = false) =
      _root_.MIPStarRE.QPBT.outcomeEventWeight S.toStrategy
        (_root_.MIPStarRE.QPBT.ProjectiveSetting.msQuestion P x ω.1 ω.2.1 ω.2.2.1 ω.2.2.2)
        (_root_.MIPStarRE.QPBT.ProjectiveSetting.msQuestion P y ω.1 ω.2.1 ω.2.2.1 ω.2.2.2)
        (fun A B => _root_.MIPStarRE.QPBT.msWinPredicate x y
          (_root_.MIPStarRE.QPBT.ProjectiveSetting.msAnswerOrZero x A)
          (_root_.MIPStarRE.QPBT.ProjectiveSetting.msAnswerOrZero y B) = false) := by
  let qx := _root_.MIPStarRE.QPBT.ProjectiveSetting.msQuestion P x
    ω.1 ω.2.1 ω.2.2.1 ω.2.2.2
  let qy := _root_.MIPStarRE.QPBT.ProjectiveSetting.msQuestion P y
    ω.1 ω.2.1 ω.2.2.1 ω.2.2.2
  let fA : (_root_.MIPStarRE.QPBT.pauliBasisTest P).AnswerA → _root_.MIPStarRE.QPBT.MsAnswer :=
    _root_.MIPStarRE.QPBT.ProjectiveSetting.msAnswerOrZero (P := P) x
  let fB : (_root_.MIPStarRE.QPBT.pauliBasisTest P).AnswerB → _root_.MIPStarRE.QPBT.MsAnswer :=
    _root_.MIPStarRE.QPBT.ProjectiveSetting.msAnswerOrZero (P := P) y
  have hmass (a b : _root_.MIPStarRE.QPBT.MsAnswer) :
      _root_.MIPStarRE.QPBT.outcomeWeight (S.msStrategyAt ω) x y a b =
        ∑ A ∈ Finset.univ.filter (fun A => fA A = a),
          ∑ B ∈ Finset.univ.filter (fun B => fB B = b),
            _root_.MIPStarRE.QPBT.outcomeWeight S.toStrategy qx qy A B := by
    have hop :
        _root_.MIPStarRE.QPBT.heteroKron
            (∑ A ∈ Finset.univ.filter (fun A => fA A = a),
              (S.toStrategy.A qx).effect A)
            (∑ B ∈ Finset.univ.filter (fun B => fB B = b),
              (S.toStrategy.B qy).effect B) =
          ∑ A ∈ Finset.univ.filter (fun A => fA A = a),
            ∑ B ∈ Finset.univ.filter (fun B => fB B = b),
              _root_.MIPStarRE.QPBT.heteroKron ((S.toStrategy.A qx).effect A)
                ((S.toStrategy.B qy).effect B) := by
      ext i j
      simp only [Matrix.sum_apply, _root_.MIPStarRE.QPBT.heteroKron, Matrix.kronecker,
        Matrix.kroneckerMap_apply]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro A _
      rw [Finset.mul_sum]
    change _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm S.toStrategy.ψ
        (_root_.MIPStarRE.QPBT.heteroKron
          (((S.toStrategy.A qx).postprocess fA).effect a)
          (((S.toStrategy.B qy).postprocess fB).effect b)) = _
    simp only [_root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect]
    rw [hop]
    simp [_root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm, _root_.MIPStarRE.QPBT.applyOperatorToState, _root_.MIPStarRE.QPBT.outcomeWeight]
  unfold _root_.MIPStarRE.QPBT.outcomeEventWeight
  simp_rw [hmass]
  symm
  calc
    (∑ A, ∑ B, if _root_.MIPStarRE.QPBT.msWinPredicate x y (fA A) (fB B) = false then
        _root_.MIPStarRE.QPBT.outcomeWeight S.toStrategy qx qy A B else 0) =
        ∑ a : _root_.MIPStarRE.QPBT.MsAnswer, ∑ A ∈ Finset.univ.filter (fun A => fA A = a),
          ∑ B, if _root_.MIPStarRE.QPBT.msWinPredicate x y (fA A) (fB B) = false then
            _root_.MIPStarRE.QPBT.outcomeWeight S.toStrategy qx qy A B else 0 := by
      exact (Finset.sum_fiberwise Finset.univ fA (fun A =>
        ∑ B, if _root_.MIPStarRE.QPBT.msWinPredicate x y (fA A) (fB B) = false then
          _root_.MIPStarRE.QPBT.outcomeWeight S.toStrategy qx qy A B else 0)).symm
    _ = ∑ a : _root_.MIPStarRE.QPBT.MsAnswer, ∑ A ∈ Finset.univ.filter (fun A => fA A = a),
        ∑ B, if _root_.MIPStarRE.QPBT.msWinPredicate x y a (fB B) = false then
          _root_.MIPStarRE.QPBT.outcomeWeight S.toStrategy qx qy A B else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro A hA
      rw [(Finset.mem_filter.mp hA).2]
    _ = ∑ a : _root_.MIPStarRE.QPBT.MsAnswer, ∑ A ∈ Finset.univ.filter (fun A => fA A = a),
        ∑ b : _root_.MIPStarRE.QPBT.MsAnswer, ∑ B ∈ Finset.univ.filter (fun B => fB B = b),
          if _root_.MIPStarRE.QPBT.msWinPredicate x y a (fB B) = false then
            _root_.MIPStarRE.QPBT.outcomeWeight S.toStrategy qx qy A B else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro A _
      exact (Finset.sum_fiberwise Finset.univ fB (fun B =>
        if _root_.MIPStarRE.QPBT.msWinPredicate x y a (fB B) = false then
          _root_.MIPStarRE.QPBT.outcomeWeight S.toStrategy qx qy A B else 0)).symm
    _ = ∑ a : _root_.MIPStarRE.QPBT.MsAnswer, ∑ A ∈ Finset.univ.filter (fun A => fA A = a),
        ∑ b : _root_.MIPStarRE.QPBT.MsAnswer, ∑ B ∈ Finset.univ.filter (fun B => fB B = b),
          if _root_.MIPStarRE.QPBT.msWinPredicate x y a b = false then
            _root_.MIPStarRE.QPBT.outcomeWeight S.toStrategy qx qy A B else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro A _
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro B hB
      rw [(Finset.mem_filter.mp hB).2]
    _ = ∑ a : _root_.MIPStarRE.QPBT.MsAnswer, ∑ b : _root_.MIPStarRE.QPBT.MsAnswer,
        ∑ A ∈ Finset.univ.filter (fun A => fA A = a),
          ∑ B ∈ Finset.univ.filter (fun B => fB B = b),
            if _root_.MIPStarRE.QPBT.msWinPredicate x y a b = false then
              _root_.MIPStarRE.QPBT.outcomeWeight S.toStrategy qx qy A B else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = ∑ a : _root_.MIPStarRE.QPBT.MsAnswer, ∑ b : _root_.MIPStarRE.QPBT.MsAnswer,
        if _root_.MIPStarRE.QPBT.msWinPredicate x y a b = false then
          ∑ A ∈ Finset.univ.filter (fun A => fA A = a),
            ∑ B ∈ Finset.univ.filter (fun B => fB B = b),
              _root_.MIPStarRE.QPBT.outcomeWeight S.toStrategy qx qy A B
        else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      by_cases hab : _root_.MIPStarRE.QPBT.msWinPredicate x y a b = false <;> simp [hab]
