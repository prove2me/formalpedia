-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Pasting.verticalLine_pointAt_appendPoint
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T16:44:31.34873+00:00
-- url     : https://prove2.me/submissions/5fe6095d-a846-46f1-b5ef-0a073887d7ca

-- Generated proof for MIPStarRE.LDT.Pasting.verticalLine_pointAt_appendPoint.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionUniformSums
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomialEmbedding
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_MeasurementLift
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OperatorExpectations
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFAverages
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFUniformAverages
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_TensorPlacement
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_Approximation
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Families
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Interpolation
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Tuples
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Sandwich_GHatSandwich
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Sandwich_Switcheroo
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_QuantumNonneg
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyFailures
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyPolynomialFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyRole_Algebra
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyRole_Core
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace LIDT

end LIDT

open LIDT
/-!
# Section 12 — Sandwich constructions: pasted families

Pasted interpolation families, recurrence weights, and final operator families.
-/

@[expose] public section

open LIDT.MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem solution
    (params : _root_.LIDT.MIPStarRE.LDT.Parameters) [_root_.LIDT.MIPStarRE.LDT.FieldModel params.q]
    (u : _root_.LIDT.MIPStarRE.LDT.Point params) (x : _root_.LIDT.MIPStarRE.LDT.Fq params) :
    ({ base := _root_.LIDT.MIPStarRE.LDT.appendPoint params u _root_.LIDT.MIPStarRE.LDT.zeroCoord,
       direction := _root_.LIDT.MIPStarRE.LDT.lastCoord params } : _root_.LIDT.MIPStarRE.LDT.AxisParallelLine params.next).pointAt x =
      _root_.LIDT.MIPStarRE.LDT.appendPoint params u x := by
  ext i
  by_cases hlast : i = _root_.LIDT.MIPStarRE.LDT.lastCoord params
  · subst i
    have hzero :
        _root_.LIDT.MIPStarRE.LDT.addCoord (params := params.next) (_root_.LIDT.MIPStarRE.LDT.zeroCoord (params := params)) x = x := by
      change _root_.LIDT.MIPStarRE.LDT.addCoord (params := params) _root_.LIDT.MIPStarRE.LDT.zeroCoord x = x
      unfold _root_.LIDT.MIPStarRE.LDT.addCoord _root_.LIDT.MIPStarRE.LDT.zeroCoord
      rw [_root_.LIDT.MIPStarRE.LDT.decode_encodeScalar]
      simp
    simpa [_root_.LIDT.MIPStarRE.LDT.AxisParallelLine.pointAt, _root_.LIDT.MIPStarRE.LDT.appendPoint, _root_.LIDT.MIPStarRE.LDT.lastCoord,
      Nat.lt_irrefl] using congrArg Fin.val hzero
  · have him : i.1 < params.m := by
      have hi_lt : i.1 < params.m + 1 := by simpa [_root_.LIDT.MIPStarRE.LDT.Parameters.next] using i.2
      by_cases hlt : i.1 < params.m
      · exact hlt
      · have hi_eq : i.1 = params.m := by omega
        have hi_last : i = _root_.LIDT.MIPStarRE.LDT.lastCoord params := by
          apply Fin.ext
          simp [_root_.LIDT.MIPStarRE.LDT.lastCoord, hi_eq]
        exact (hlast hi_last).elim
    simp [_root_.LIDT.MIPStarRE.LDT.AxisParallelLine.pointAt, _root_.LIDT.MIPStarRE.LDT.appendPoint, him, hlast]
