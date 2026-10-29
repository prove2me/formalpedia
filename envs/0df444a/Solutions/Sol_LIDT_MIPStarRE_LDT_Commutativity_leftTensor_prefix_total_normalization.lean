-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Commutativity.leftTensor_prefix_total_normalization
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T13:50:29.496917+00:00
-- url     : https://prove2.me/submissions/62abfe33-13b7-4513-8169-73875e4adf98

-- Generated proof for MIPStarRE.LDT.Commutativity.leftTensor_prefix_total_normalization.
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
    (A : _root_.LIDT.MIPStarRE.LDT.SubMeas α ι) (B : _root_.LIDT.MIPStarRE.LDT.SubMeas β ι)
    (T : _root_.LIDT.MIPStarRE.Quantum.Op ι)
    (hT_nonneg : 0 ≤ T) (hT_le_one : T ≤ 1) :
    ∑ ab : α × β,
        _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A.outcome ab.1 * B.outcome ab.2 * T) *
          (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A.outcome ab.1 * B.outcome ab.2 * T))ᴴ ≤
      (1 : _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι)) := by
  classical
  let X : α × β → _root_.LIDT.MIPStarRE.Quantum.Op ι := fun ab =>
    A.outcome ab.1 * B.outcome ab.2 * T
  have hT_herm : Tᴴ = T :=
    (Matrix.nonneg_iff_posSemidef.mp hT_nonneg).isHermitian.eq
  have hT_sq_le_one : T * T ≤ (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) := by
    exact le_trans (_root_.LIDT.MIPStarRE.Quantum.sq_le_self hT_nonneg hT_le_one) hT_le_one
  have hterm_le : ∀ a b,
      X (a, b) * (X (a, b))ᴴ ≤
        A.outcome a * (B.outcome b * B.outcome b) * A.outcome a := by
    intro a b
    have hB_sandwich :
        B.outcome b * (T * T) * B.outcome b ≤
          B.outcome b * (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) * B.outcome b :=
      IsSelfAdjoint.conjugate_le_conjugate hT_sq_le_one (B.outcome_hermitian b)
    have hA_sandwich :
        A.outcome a * (B.outcome b * (T * T) * B.outcome b) * A.outcome a ≤
          A.outcome a *
            (B.outcome b * (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) * B.outcome b) *
            A.outcome a :=
      IsSelfAdjoint.conjugate_le_conjugate hB_sandwich (A.outcome_hermitian a)
    calc
      X (a, b) * (X (a, b))ᴴ
          = A.outcome a * (B.outcome b * (T * T) * B.outcome b) * A.outcome a := by
            simp only [X, Matrix.conjTranspose_mul, hT_herm, A.outcome_hermitian a,
              B.outcome_hermitian b]
            simp only [mul_assoc]
      _ ≤ A.outcome a *
            (B.outcome b * (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) * B.outcome b) *
            A.outcome a := hA_sandwich
      _ = A.outcome a * (B.outcome b * B.outcome b) * A.outcome a := by
            simp [mul_assoc]
  have hrow_le : ∀ a : α,
      ∑ b : β, X (a, b) * (X (a, b))ᴴ ≤ A.outcome a := by
    intro a
    have hBsq_sum :
        ∑ b : β, B.outcome b * B.outcome b ≤ B.total := by
      calc
        ∑ b : β, B.outcome b * B.outcome b
            ≤ ∑ b : β, B.outcome b := by
              exact Finset.sum_le_sum fun b _ =>
                _root_.LIDT.MIPStarRE.Quantum.sq_le_self (B.outcome_pos b) (B.outcome_le_one b)
        _ = B.total := B.sum_eq_total
    calc
      ∑ b : β, X (a, b) * (X (a, b))ᴴ
          ≤ ∑ b : β, A.outcome a * (B.outcome b * B.outcome b) * A.outcome a := by
            exact Finset.sum_le_sum fun b _ => hterm_le a b
      _ = A.outcome a * (∑ b : β, B.outcome b * B.outcome b) * A.outcome a := by
            rw [← Matrix.sum_mul, ← Matrix.mul_sum]
      _ ≤ A.outcome a * B.total * A.outcome a := by
            exact IsSelfAdjoint.conjugate_le_conjugate hBsq_sum (A.outcome_hermitian a)
      _ ≤ A.outcome a * (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) * A.outcome a := by
            exact IsSelfAdjoint.conjugate_le_conjugate B.total_le_one (A.outcome_hermitian a)
      _ = A.outcome a * A.outcome a := by simp
      _ ≤ A.outcome a :=
            _root_.LIDT.MIPStarRE.Quantum.sq_le_self (A.outcome_pos a) (A.outcome_le_one a)
  have hbase : ∑ ab : α × β, X ab * (X ab)ᴴ ≤ (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) := by
    calc
      ∑ ab : α × β, X ab * (X ab)ᴴ
          = ∑ a : α, ∑ b : β, X (a, b) * (X (a, b))ᴴ := by
            simpa using
              (Fintype.sum_prod_type' (f := fun a : α => fun b : β =>
                X (a, b) * (X (a, b))ᴴ))
      _ ≤ ∑ a : α, A.outcome a := by
            exact Finset.sum_le_sum fun a _ => hrow_le a
      _ = A.total := A.sum_eq_total
      _ ≤ 1 := A.total_le_one
  calc
    ∑ ab : α × β,
        _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A.outcome ab.1 * B.outcome ab.2 * T) *
          (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A.outcome ab.1 * B.outcome ab.2 * T))ᴴ
      = _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (∑ ab : α × β, X ab * (X ab)ᴴ) := by
          calc
            ∑ ab : α × β,
                _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A.outcome ab.1 * B.outcome ab.2 * T) *
                  (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A.outcome ab.1 * B.outcome ab.2 * T))ᴴ
                = ∑ ab : α × β, _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (X ab * (X ab)ᴴ) := by
                  refine Finset.sum_congr rfl ?_
                  intro ab _
                  have hleft_adj :
                      (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (X ab))ᴴ =
                        _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) ((X ab)ᴴ) := by
                    simpa [_root_.LIDT.MIPStarRE.LDT.leftTensor, _root_.LIDT.MIPStarRE.LDT.opTensor] using
                      (_root_.LIDT.MIPStarRE.LDT.conjTranspose_opTensor (ι₁ := ι) (ι₂ := ι) (X ab)
                        (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι))
                  simp [X, hleft_adj, _root_.LIDT.MIPStarRE.LDT.leftTensor_mul_leftTensor]
              _ = _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (∑ ab : α × β, X ab * (X ab)ᴴ) := by
                  rw [← _root_.LIDT.MIPStarRE.LDT.leftTensor_finset_sum (ι₂ := ι) Finset.univ
                    (fun ab : α × β => X ab * (X ab)ᴴ)]
    _ ≤ 1 := _root_.LIDT.MIPStarRE.LDT.leftTensor_le_one (ι₂ := ι) hbase
