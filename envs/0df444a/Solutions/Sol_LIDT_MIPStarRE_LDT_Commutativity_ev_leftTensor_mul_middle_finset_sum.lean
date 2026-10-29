-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Commutativity.ev_leftTensor_mul_middle_finset_sum
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T13:54:09.631663+00:00
-- url     : https://prove2.me/submissions/1fec36dc-bfd4-4b18-b492-bf4ed0e9981b

-- Generated proof for MIPStarRE.LDT.Commutativity.ev_leftTensor_mul_middle_finset_sum.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionUniformSums
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Normalization
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Stability
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Products
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
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

namespace LIDT.MIPStarRE.LDT.Commutativity
end LIDT.MIPStarRE.LDT.Commutativity

namespace LIDT

end LIDT

open LIDT
/-!
# Reindexing and evaluation utilities for the evaluated-slice paper chain

This file contains finite-reindexing and evaluated-family identities used by
the paper-faithful scalar approximation chain.
-/

@[expose] public section

open LIDT.MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem solution
    {α : Type*} (s : Finset α)
    (ψ : _root_.LIDT.MIPStarRE.LDT.QuantumState (ι × ι))
    (A C R D : _root_.LIDT.MIPStarRE.Quantum.Op ι)
    (B : α → _root_.LIDT.MIPStarRE.Quantum.Op ι) :
    _root_.LIDT.MIPStarRE.LDT.ev ψ
        (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (((A * (∑ x ∈ s, B x) * C) * R)) *
          _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) D) =
      ∑ x ∈ s,
        _root_.LIDT.MIPStarRE.LDT.ev ψ
          (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (((A * B x * C) * R)) *
            _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) D) := by
  classical
  have hinner :
      ((A * (∑ x ∈ s, B x) * C) * R) =
        ∑ x ∈ s, ((A * B x * C) * R) := by
    simp [Matrix.mul_sum, Finset.sum_mul, mul_assoc]
  calc
    _root_.LIDT.MIPStarRE.LDT.ev ψ
        (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (((A * (∑ x ∈ s, B x) * C) * R)) *
          _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) D)
        = _root_.LIDT.MIPStarRE.LDT.ev ψ
            (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (∑ x ∈ s, ((A * B x * C) * R)) *
              _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) D) := by rw [hinner]
    _ = _root_.LIDT.MIPStarRE.LDT.ev ψ
          ((∑ x ∈ s, _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (((A * B x * C) * R))) *
            _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) D) := by
          rw [_root_.LIDT.MIPStarRE.LDT.leftTensor_finset_sum (ι₂ := ι)]
    _ = _root_.LIDT.MIPStarRE.LDT.ev ψ
          (∑ x ∈ s,
            _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (((A * B x * C) * R) ) *
              _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) D) := by
          rw [Finset.sum_mul]
    _ = ∑ x ∈ s,
          _root_.LIDT.MIPStarRE.LDT.ev ψ
            (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (((A * B x * C) * R)) *
              _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) D) := by
          rw [_root_.LIDT.MIPStarRE.LDT.ev_finset_sum]
