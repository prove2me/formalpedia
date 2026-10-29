-- Prove2me | solution 1 for MIPStarRE.QPBT.consistencyDefect_padState_compressAt
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:34:37.407947+00:00
-- url     : https://prove2.me/submissions/8f747a09-13a7-41e2-9f91-eb84c43f8043

-- Generated proof for MIPStarRE.QPBT.consistencyDefect_padState_compressAt.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
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
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_MeasurementCompression
import Definitions.Def_QPBT_QPBT_Games_StrategyClasses

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace LIDT.MIPStarRE.Quantum.Measurement
end LIDT.MIPStarRE.Quantum.Measurement
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.Measurement
end MIPStarRE.QPBT.Measurement

/-!
# Ground-slice compression of measurements

This module restricts a POVM on a product space to one distinguished ancillary
coordinate. It also records that this restriction commutes with deterministic
outcome postprocessing, recovers a POVM from its one-measurement Naimark
dilation, and preserves consistency defects evaluated on the correspondingly
padded bipartite state.

The construction supports the pullback after the first paragraph of the proof
of paper `lem:qld-4-7`,
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1279-1289`.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open LIDT.MIPStarRE.Quantum.Measurement









open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum

open MIPStarRE.QPBT.Measurement

theorem solution
    {X Outcome I J κA κB : Type*}
    [Fintype X] [DecidableEq X]
    [Fintype Outcome] [DecidableEq Outcome]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    [Fintype κA] [DecidableEq κA] [Fintype κB] [DecidableEq κB]
    (μ : _root_.LIDT.MIPStarRE.LDT.Distribution X)
    (MA : X → _root_.LIDT.MIPStarRE.Quantum.Measurement Outcome (I × κA))
    (MB : X → _root_.LIDT.MIPStarRE.Quantum.Measurement Outcome (J × κB))
    (a₀ : κA) (b₀ : κB) (ψ : EuclideanSpace ℂ (I × J)) :
    _root_.MIPStarRE.QPBT.consistencyDefect μ
        (fun x a => _root_.MIPStarRE.QPBT.heteroKron ((MA x).effect a) 1)
        (fun x a => _root_.MIPStarRE.QPBT.heteroKron 1 ((MB x).effect a))
        (_root_.MIPStarRE.QPBT.padState a₀ b₀ ψ) =
      _root_.MIPStarRE.QPBT.consistencyDefect μ
        (fun x a => _root_.MIPStarRE.QPBT.heteroKron (((MA x).compressAt a₀).effect a) 1)
        (fun x a => _root_.MIPStarRE.QPBT.heteroKron 1 (((MB x).compressAt b₀).effect a))
        ψ := by
  unfold _root_.MIPStarRE.QPBT.consistencyDefect
  apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
  intro x
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  by_cases hab : a = b
  · simp [hab]
  · simp only [hab, if_false]
    change _root_.MIPStarRE.QPBT.vectorQForm (_root_.MIPStarRE.QPBT.padState a₀ b₀ ψ)
        (_root_.MIPStarRE.QPBT.heteroKron ((MA x).effect a) 1 * _root_.MIPStarRE.QPBT.heteroKron 1 ((MB x).effect b)) =
      _root_.MIPStarRE.QPBT.vectorQForm ψ
        (_root_.MIPStarRE.QPBT.heteroKron (((MA x).compressAt a₀).effect a) 1 *
          _root_.MIPStarRE.QPBT.heteroKron 1 (((MB x).compressAt b₀).effect b))
    simpa only [_root_.MIPStarRE.QPBT.heteroKron_mul, Matrix.mul_one, Matrix.one_mul] using
      _root_.MIPStarRE.QPBT.stateQForm_padState a₀ b₀ ψ
        (((MA x).compressAt a₀).effect a)
        (((MB x).compressAt b₀).effect b)
        ((MA x).effect a) ((MB x).effect b)
        (fun i j => rfl) (fun i j => rfl)
