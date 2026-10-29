-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Commutativity.leftTensor_pair_prefix_normalization
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T13:50:29.558992+00:00
-- url     : https://prove2.me/submissions/eee11cd4-cd35-4916-9668-82c16d973822

-- Generated proof for MIPStarRE.LDT.Commutativity.leftTensor_pair_prefix_normalization.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_QuantumNonneg
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyPolynomialFamilies
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

open scoped _root_.Matrix

namespace LIDT.MIPStarRE.LDT.Commutativity
end LIDT.MIPStarRE.LDT.Commutativity
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries

namespace LIDT

end LIDT

open LIDT
/-!
# Tensor normalization helpers for the evaluated-slice paper chain

This file contains the normalization estimates used as side conditions for
`closenessOfIP` and its adjoint form in the scalar approximation chain.
-/

@[expose] public section

open LIDT.MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem solution
    {α β : Type*} [Fintype α] [Fintype β]
    (A : _root_.LIDT.MIPStarRE.LDT.SubMeas α ι) (B : _root_.LIDT.MIPStarRE.LDT.SubMeas β ι) :
    ∑ b : β,
        (∑ a : α, _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A.outcome a * B.outcome b)) *
        (∑ a : α, _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A.outcome a * B.outcome b))ᴴ ≤
      (1 : _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι)) := by
  classical
  let T : β → _root_.LIDT.MIPStarRE.Quantum.Op ι := fun b => A.total * B.outcome b
  have hAtotal_herm : A.totalᴴ = A.total :=
    (Matrix.nonneg_iff_posSemidef.mp A.total_nonneg).isHermitian.eq
  have hbase : ∑ b : β, T b * (T b)ᴴ ≤ (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) := by
    calc
      ∑ b : β, T b * (T b)ᴴ
          = ∑ b : β, A.total * (B.outcome b * B.outcome b) * A.total := by
            refine Finset.sum_congr rfl ?_
            intro b _
            simp only [T, Matrix.conjTranspose_mul, hAtotal_herm, B.outcome_hermitian b]
            simp only [mul_assoc]
      _ ≤ ∑ b : β, A.total * B.outcome b * A.total := by
            exact Finset.sum_le_sum fun b _ =>
              IsSelfAdjoint.conjugate_le_conjugate
                (_root_.LIDT.MIPStarRE.Quantum.sq_le_self (B.outcome_pos b) (B.outcome_le_one b))
                hAtotal_herm
      _ = A.total * B.total * A.total := by
            rw [← Matrix.sum_mul, ← Matrix.mul_sum, B.sum_eq_total]
      _ ≤ A.total * (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) * A.total := by
            exact IsSelfAdjoint.conjugate_le_conjugate B.total_le_one hAtotal_herm
      _ = A.total * A.total := by simp
      _ ≤ A.total := _root_.LIDT.MIPStarRE.Quantum.sq_le_self A.total_nonneg A.total_le_one
      _ ≤ 1 := A.total_le_one
  calc
    ∑ b : β,
        (∑ a : α, _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A.outcome a * B.outcome b)) *
        (∑ a : α, _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A.outcome a * B.outcome b))ᴴ
      = ∑ b : β, _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (T b * (T b)ᴴ) := by
          refine Finset.sum_congr rfl ?_
          intro b _
          have hsum : (∑ a : α, _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A.outcome a * B.outcome b)) =
              _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (T b) := by
            rw [_root_.LIDT.MIPStarRE.LDT.leftTensor_finset_sum (ι₂ := ι) Finset.univ
              (fun a : α => A.outcome a * B.outcome b)]
            rw [← Matrix.sum_mul, A.sum_eq_total]
          rw [hsum]
          have hleft_adj : (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (T b))ᴴ = _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) ((T b)ᴴ) := by
            simpa [_root_.LIDT.MIPStarRE.LDT.leftTensor, _root_.LIDT.MIPStarRE.LDT.opTensor] using
              (_root_.LIDT.MIPStarRE.LDT.conjTranspose_opTensor (ι₁ := ι) (ι₂ := ι) (T b) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι))
          rw [hleft_adj, _root_.LIDT.MIPStarRE.LDT.leftTensor_mul_leftTensor]
    _ = _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (∑ b : β, T b * (T b)ᴴ) := by
          rw [← _root_.LIDT.MIPStarRE.LDT.leftTensor_finset_sum (ι₂ := ι) Finset.univ (fun b => T b * (T b)ᴴ)]
    _ ≤ 1 := _root_.LIDT.MIPStarRE.LDT.leftTensor_le_one (ι₂ := ι) hbase
