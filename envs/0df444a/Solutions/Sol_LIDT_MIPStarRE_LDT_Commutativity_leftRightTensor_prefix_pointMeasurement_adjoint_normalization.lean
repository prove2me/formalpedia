-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Commutativity.leftRightTensor_prefix_pointMeasurement_adjoint_normalization
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T13:50:29.848555+00:00
-- url     : https://prove2.me/submissions/78f04620-ee25-45f6-b997-0179e0be49fb

-- Generated proof for MIPStarRE.LDT.Commutativity.leftRightTensor_prefix_pointMeasurement_adjoint_normalization.
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
    (A : _root_.LIDT.MIPStarRE.LDT.SubMeas α ι) (B : _root_.LIDT.MIPStarRE.LDT.SubMeas β ι) (R : _root_.LIDT.MIPStarRE.LDT.ProjMeas β ι) :
    ∑ a : α,
        (∑ b : β,
          _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A.outcome a * B.outcome b) *
            _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (R.outcome b))ᴴ *
        (∑ b : β,
          _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A.outcome a * B.outcome b) *
            _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (R.outcome b)) ≤
      (1 : _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι)) := by
  classical
  let D : α → _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι) := fun a =>
    ∑ b : β,
      _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A.outcome a * B.outcome b) *
        _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (R.outcome b)
  have hrow_expand : ∀ a : α,
      (D a)ᴴ * D a =
        ∑ b : β,
          _root_.LIDT.MIPStarRE.LDT.opTensor (B.outcome b * (A.outcome a * A.outcome a) * B.outcome b)
            (R.outcome b) := by
    intro a
    unfold D
    calc
      (∑ b : β,
          _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A.outcome a * B.outcome b) *
            _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (R.outcome b))ᴴ *
          (∑ b : β,
            _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A.outcome a * B.outcome b) *
              _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (R.outcome b))
        = (∑ c : β,
              (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A.outcome a * B.outcome c) *
                _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (R.outcome c))ᴴ) *
            (∑ b : β,
              _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A.outcome a * B.outcome b) *
                _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (R.outcome b)) := by
              rw [Matrix.conjTranspose_sum]
      _ = ∑ c : β, ∑ b : β,
            (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A.outcome a * B.outcome c) *
              _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (R.outcome c))ᴴ *
            (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A.outcome a * B.outcome b) *
              _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (R.outcome b)) := by
              rw [Finset.sum_mul]
              refine Finset.sum_congr rfl ?_
              intro c _
              rw [Finset.mul_sum]
      _ = ∑ b : β,
            (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A.outcome a * B.outcome b) *
              _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (R.outcome b))ᴴ *
            (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A.outcome a * B.outcome b) *
              _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (R.outcome b)) := by
              refine Finset.sum_congr rfl ?_
              intro c _
              rw [Finset.sum_eq_single c]
              · intro b _ hbc
                have hcb : c ≠ b := fun h => hbc h.symm
                have horth : R.outcome c * R.outcome b = 0 :=
                  R.outcome_orthogonal c b hcb
                calc
                  (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A.outcome a * B.outcome c) *
                      _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (R.outcome c))ᴴ *
                    (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A.outcome a * B.outcome b) *
                      _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (R.outcome b))
                    = (_root_.LIDT.MIPStarRE.LDT.opTensor (A.outcome a * B.outcome c) (R.outcome c))ᴴ *
                        _root_.LIDT.MIPStarRE.LDT.opTensor (A.outcome a * B.outcome b) (R.outcome b) := by
                        rw [_root_.LIDT.MIPStarRE.LDT.leftTensor_mul_rightTensor_eq_opTensor,
                          _root_.LIDT.MIPStarRE.LDT.leftTensor_mul_rightTensor_eq_opTensor]
                  _ = _root_.LIDT.MIPStarRE.LDT.opTensor ((A.outcome a * B.outcome c)ᴴ) ((R.outcome c)ᴴ) *
                        _root_.LIDT.MIPStarRE.LDT.opTensor (A.outcome a * B.outcome b) (R.outcome b) := by
                        rw [_root_.LIDT.MIPStarRE.LDT.conjTranspose_opTensor]
                  _ = _root_.LIDT.MIPStarRE.LDT.opTensor (((A.outcome a * B.outcome c)ᴴ) *
                          (A.outcome a * B.outcome b))
                        ((R.outcome c)ᴴ * R.outcome b) := by
                        rw [_root_.LIDT.MIPStarRE.LDT.opTensor_mul]
                  _ = 0 := by
                        have hRherm : (R.outcome c)ᴴ = R.outcome c :=
                          R.outcome_hermitian c
                        rw [hRherm, horth]
                        simp [_root_.LIDT.MIPStarRE.LDT.opTensor]
              · simp
      _ = ∑ b : β,
          _root_.LIDT.MIPStarRE.LDT.opTensor (B.outcome b * (A.outcome a * A.outcome a) * B.outcome b)
            (R.outcome b) := by
              refine Finset.sum_congr rfl ?_
              intro b _
              calc
                (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A.outcome a * B.outcome b) *
                    _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (R.outcome b))ᴴ *
                  (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A.outcome a * B.outcome b) *
                    _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (R.outcome b))
                  = (_root_.LIDT.MIPStarRE.LDT.opTensor (A.outcome a * B.outcome b) (R.outcome b))ᴴ *
                      _root_.LIDT.MIPStarRE.LDT.opTensor (A.outcome a * B.outcome b) (R.outcome b) := by
                      rw [_root_.LIDT.MIPStarRE.LDT.leftTensor_mul_rightTensor_eq_opTensor]
                _ = _root_.LIDT.MIPStarRE.LDT.opTensor ((A.outcome a * B.outcome b)ᴴ) ((R.outcome b)ᴴ) *
                      _root_.LIDT.MIPStarRE.LDT.opTensor (A.outcome a * B.outcome b) (R.outcome b) := by
                      rw [_root_.LIDT.MIPStarRE.LDT.conjTranspose_opTensor]
                _ = _root_.LIDT.MIPStarRE.LDT.opTensor (((A.outcome a * B.outcome b)ᴴ) *
                        (A.outcome a * B.outcome b))
                      ((R.outcome b)ᴴ * R.outcome b) := by
                      rw [_root_.LIDT.MIPStarRE.LDT.opTensor_mul]
                _ = _root_.LIDT.MIPStarRE.LDT.opTensor (B.outcome b * (A.outcome a * A.outcome a) * B.outcome b)
                      (R.outcome b) := by
                      have hABadj : (A.outcome a * B.outcome b)ᴴ =
                          B.outcome b * A.outcome a := by
                        rw [Matrix.conjTranspose_mul, A.outcome_hermitian a,
                          B.outcome_hermitian b]
                      have hRherm : (R.outcome b)ᴴ = R.outcome b :=
                        R.outcome_hermitian b
                      rw [hABadj, hRherm, R.proj b]
                      congr 1
                      noncomm_ring
  have hsum_sq_le_one :
      ∑ a : α, A.outcome a * A.outcome a ≤ (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) := by
    calc
      ∑ a : α, A.outcome a * A.outcome a
          ≤ ∑ a : α, A.outcome a := by
            exact Finset.sum_le_sum fun a _ =>
              _root_.LIDT.MIPStarRE.Quantum.sq_le_self (A.outcome_pos a) (A.outcome_le_one a)
      _ = A.total := A.sum_eq_total
      _ ≤ 1 := A.total_le_one
  have hsum_for_b : ∀ b : β,
      ∑ a : α, B.outcome b * (A.outcome a * A.outcome a) * B.outcome b ≤
        B.outcome b := by
    intro b
    calc
      ∑ a : α, B.outcome b * (A.outcome a * A.outcome a) * B.outcome b
          = B.outcome b * (∑ a : α, A.outcome a * A.outcome a) * B.outcome b := by
            rw [← Matrix.sum_mul, ← Matrix.mul_sum]
      _ ≤ B.outcome b * (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) * B.outcome b := by
            exact IsSelfAdjoint.conjugate_le_conjugate hsum_sq_le_one (B.outcome_hermitian b)
      _ = B.outcome b * B.outcome b := by simp
      _ ≤ B.outcome b :=
            _root_.LIDT.MIPStarRE.Quantum.sq_le_self (B.outcome_pos b) (B.outcome_le_one b)
  calc
    ∑ a : α,
        (∑ b : β,
          _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A.outcome a * B.outcome b) *
            _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (R.outcome b))ᴴ *
        (∑ b : β,
          _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A.outcome a * B.outcome b) *
            _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (R.outcome b))
      = ∑ a : α, (D a)ᴴ * D a := by rfl
    _ = ∑ b : β, ∑ a : α,
          _root_.LIDT.MIPStarRE.LDT.opTensor (B.outcome b * (A.outcome a * A.outcome a) * B.outcome b)
            (R.outcome b) := by
          calc
            ∑ a : α, (D a)ᴴ * D a
                = ∑ a : α, ∑ b : β,
                    _root_.LIDT.MIPStarRE.LDT.opTensor (B.outcome b * (A.outcome a * A.outcome a) * B.outcome b)
                      (R.outcome b) := by
                  exact Finset.sum_congr rfl fun a _ => hrow_expand a
            _ = ∑ b : β, ∑ a : α,
                    _root_.LIDT.MIPStarRE.LDT.opTensor (B.outcome b * (A.outcome a * A.outcome a) * B.outcome b)
                      (R.outcome b) := by
                  rw [Finset.sum_comm]
    _ ≤ ∑ b : β, _root_.LIDT.MIPStarRE.LDT.opTensor (B.outcome b) (R.outcome b) := by
          refine Finset.sum_le_sum ?_
          intro b _
          calc
            ∑ a : α,
                _root_.LIDT.MIPStarRE.LDT.opTensor (B.outcome b * (A.outcome a * A.outcome a) * B.outcome b)
                  (R.outcome b)
              = _root_.LIDT.MIPStarRE.LDT.opTensor (∑ a : α,
                  B.outcome b * (A.outcome a * A.outcome a) * B.outcome b)
                  (R.outcome b) := by
                  rw [_root_.LIDT.MIPStarRE.LDT.opTensor_sum_left_univ]
            _ ≤ _root_.LIDT.MIPStarRE.LDT.opTensor (B.outcome b) (R.outcome b) := by
                  exact _root_.LIDT.MIPStarRE.LDT.opTensor_mono_left (hsum_for_b b) (R.outcome_pos b)
    _ ≤ ∑ b : β, _root_.LIDT.MIPStarRE.LDT.opTensor (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) (R.outcome b) := by
          exact Finset.sum_le_sum fun b _ =>
            _root_.LIDT.MIPStarRE.LDT.opTensor_mono_left (B.outcome_le_one b) (R.outcome_pos b)
    _ = 1 := by
          calc
            ∑ b : β, _root_.LIDT.MIPStarRE.LDT.opTensor (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) (R.outcome b)
                = _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (∑ b : β, R.outcome b) := by
                  rw [_root_.LIDT.MIPStarRE.LDT.rightTensor_finset_sum]
            _ = 1 := by rw [R.sum_eq, _root_.LIDT.MIPStarRE.LDT.rightTensor_one]
