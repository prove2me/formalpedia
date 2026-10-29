-- Prove2me | solution 1 for MIPStarRE.QPBT.pointConsistency_eq_mismatch
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T00:16:03.03898+00:00
-- url     : https://prove2.me/submissions/b39b1df3-0e5a-469d-a239-8f19ca5f0387

-- Generated proof for MIPStarRE.QPBT.pointConsistency_eq_mismatch.
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
import Definitions.Def_QPBT_QPBT_Observables_PointConsistency
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Theorems.Thm_MIPStarRE_QPBT_WinImplications_consistencyDefect_postprocess_eq_mismatch
import Theorems.Thm_MIPStarRE_QPBT_consistencyDefect_congr

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.ProjectiveSetting
end MIPStarRE.QPBT.ProjectiveSetting

/-!
# Expanded point consistency and commutation

This module records the quantitative conclusions for the expanded point
measurements on each of the four register placements. No symmetry-transfer
principle is assumed: the four placements occur explicitly in the statements.

## References

The declarations formalize blueprint
`lem:qld-comm-cons`, whose paper source
is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:452-505`.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum





/-! ## Consistency of the unexpanded point measurements -/
attribute [local instance] _root_.MIPStarRE.QPBT.pauliEdgeNonemptyPointConsistency

theorem solution {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}
    (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) (W : _root_.MIPStarRE.QPBT.PauliKind) :
    _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P))
        (fun u a => _root_.MIPStarRE.QPBT.heteroKron ((S.pointMeas .alice W u).effect a) 1)
        (fun u a => _root_.MIPStarRE.QPBT.heteroKron 1 ((S.pointMeas .bob W u).effect a))
        S.toStrategy.ψ =
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P)) (fun u =>
        _root_.MIPStarRE.QPBT.outcomeEventWeight S.toStrategy
          (_root_.MIPStarRE.QPBT.ProjectiveSetting.pointQuestion P W u)
          (_root_.MIPStarRE.QPBT.ProjectiveSetting.pointQuestion P W u)
          (fun A B => _root_.MIPStarRE.QPBT.ProjectiveSetting.pointAnswerOrZero A ≠
            _root_.MIPStarRE.QPBT.ProjectiveSetting.pointAnswerOrZero B)) := by
  let X := Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P
  let q : X → _root_.MIPStarRE.QPBT.PauliQuestion P := fun u => _root_.MIPStarRE.QPBT.ProjectiveSetting.pointQuestion P W u
  let f : X → _root_.MIPStarRE.QPBT.PauliAnswer P → _root_.MIPStarRE.QPBT.PauliScalar P := fun _ =>
    _root_.MIPStarRE.QPBT.ProjectiveSetting.pointAnswerOrZero
  have h := _root_.MIPStarRE.QPBT.WinImplications.consistencyDefect_postprocess_eq_mismatch
    (X := X) (_root_.LIDT.MIPStarRE.LDT.uniformDistribution X) S.toStrategy q q f f
  have hA : ∀ (u : X) c,
      _root_.MIPStarRE.QPBT.heteroKron ((S.pointMeas .alice W u).effect c)
          (1 : _root_.LIDT.MIPStarRE.Quantum.Op S.toStrategy.ιB) =
        _root_.MIPStarRE.QPBT.heteroKron (((S.toStrategy.A (q u)).postprocess (f u)).effect c)
          (1 : _root_.LIDT.MIPStarRE.Quantum.Op S.toStrategy.ιB) := by
    intro u c
    rfl
  have hB : ∀ (u : X) c,
      _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op S.toStrategy.ιA)
          ((S.pointMeas .bob W u).effect c) =
        _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op S.toStrategy.ιA)
          (((S.toStrategy.B (q u)).postprocess (f u)).effect c) := by
    intro u c
    rfl
  calc
    _ = _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution X)
        (fun u c => _root_.MIPStarRE.QPBT.heteroKron
          (((S.toStrategy.A (q u)).postprocess (f u)).effect c) 1)
        (fun u c => _root_.MIPStarRE.QPBT.heteroKron 1
          (((S.toStrategy.B (q u)).postprocess (f u)).effect c))
        S.toStrategy.ψ :=
          _root_.MIPStarRE.QPBT.consistencyDefect_congr _ _ _ _ _ _ hA hB
    _ = _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution X) (fun u =>
        _root_.MIPStarRE.QPBT.outcomeEventWeight S.toStrategy (q u) (q u)
          (fun A B => f u A ≠ f u B)) := h
    _ = _ := by rfl
