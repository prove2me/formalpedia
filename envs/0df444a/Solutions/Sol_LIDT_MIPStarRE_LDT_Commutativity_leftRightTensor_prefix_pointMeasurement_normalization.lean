-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Commutativity.leftRightTensor_prefix_pointMeasurement_normalization
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T13:50:29.722978+00:00
-- url     : https://prove2.me/submissions/f8b8f4a2-f169-4ba1-8607-d94e03cf819d

-- Generated proof for MIPStarRE.LDT.Commutativity.leftRightTensor_prefix_pointMeasurement_normalization.
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
            _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (R.outcome b)) *
        (∑ b : β,
          _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A.outcome a * B.outcome b) *
            _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (R.outcome b))ᴴ ≤
      (1 : _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι)) := by
  classical
  let D : α → _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι) := fun a =>
    ∑ b : β,
      _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A.outcome a * B.outcome b) *
        _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (R.outcome b)
  have hrow_le : ∀ a : α, D a * (D a)ᴴ ≤ _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A.outcome a) := by
    intro a
    have hrow_expand :
        D a * (D a)ᴴ =
          ∑ b : β,
            _root_.LIDT.MIPStarRE.LDT.opTensor (A.outcome a * (B.outcome b * (B.outcome b * A.outcome a)))
              (R.outcome b) := by
      unfold D
      calc
        (∑ b : β,
            _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A.outcome a * B.outcome b) *
              _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (R.outcome b)) *
            (∑ b : β,
              _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A.outcome a * B.outcome b) *
                _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (R.outcome b))ᴴ
          = (∑ b : β,
            _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A.outcome a * B.outcome b) *
              _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (R.outcome b)) *
              (∑ c : β,
                (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A.outcome a * B.outcome c) *
                  _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (R.outcome c))ᴴ) := by
                rw [Matrix.conjTranspose_sum]
        _ = ∑ b : β, ∑ c : β,
              (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A.outcome a * B.outcome b) *
                _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (R.outcome b)) *
              (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A.outcome a * B.outcome c) *
                _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (R.outcome c))ᴴ := by
                rw [Finset.sum_mul]
                refine Finset.sum_congr rfl ?_
                intro b _
                rw [Finset.mul_sum]
        _ = ∑ b : β,
              (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A.outcome a * B.outcome b) *
                _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (R.outcome b)) *
              (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A.outcome a * B.outcome b) *
                _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (R.outcome b))ᴴ := by
                refine Finset.sum_congr rfl ?_
                intro b _
                rw [Finset.sum_eq_single b]
                · intro c _ hcb
                  have hbc : b ≠ c := fun h => hcb h.symm
                  have horth : R.outcome b * R.outcome c = 0 := R.outcome_orthogonal b c hbc
                  calc
                    (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A.outcome a * B.outcome b) *
                        _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (R.outcome b)) *
                        (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A.outcome a * B.outcome c) *
                          _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (R.outcome c))ᴴ
                      = _root_.LIDT.MIPStarRE.LDT.opTensor (A.outcome a * B.outcome b) (R.outcome b) *
                          (_root_.LIDT.MIPStarRE.LDT.opTensor (A.outcome a * B.outcome c) (R.outcome c))ᴴ := by
                          rw [_root_.LIDT.MIPStarRE.LDT.leftTensor_mul_rightTensor_eq_opTensor,
                            _root_.LIDT.MIPStarRE.LDT.leftTensor_mul_rightTensor_eq_opTensor]
                    _ = _root_.LIDT.MIPStarRE.LDT.opTensor (A.outcome a * B.outcome b) (R.outcome b) *
                          _root_.LIDT.MIPStarRE.LDT.opTensor ((A.outcome a * B.outcome c)ᴴ) ((R.outcome c)ᴴ) := by
                          rw [_root_.LIDT.MIPStarRE.LDT.conjTranspose_opTensor]
                    _ = _root_.LIDT.MIPStarRE.LDT.opTensor ((A.outcome a * B.outcome b) *
                            ((A.outcome a * B.outcome c)ᴴ))
                          (R.outcome b * (R.outcome c)ᴴ) := by
                          rw [_root_.LIDT.MIPStarRE.LDT.opTensor_mul]
                    _ = 0 := by
                          have hRherm : (R.outcome c)ᴴ = R.outcome c :=
                            R.outcome_hermitian c
                          rw [hRherm, horth]
                          simp [_root_.LIDT.MIPStarRE.LDT.opTensor]
                · simp
        _ = ∑ b : β,
            _root_.LIDT.MIPStarRE.LDT.opTensor (A.outcome a * (B.outcome b * (B.outcome b * A.outcome a)))
              (R.outcome b) := by
                refine Finset.sum_congr rfl ?_
                intro b _
                calc
                  (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A.outcome a * B.outcome b) *
                        _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (R.outcome b)) *
                      (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A.outcome a * B.outcome b) *
                        _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (R.outcome b))ᴴ
                    = _root_.LIDT.MIPStarRE.LDT.opTensor (A.outcome a * B.outcome b) (R.outcome b) *
                        (_root_.LIDT.MIPStarRE.LDT.opTensor (A.outcome a * B.outcome b) (R.outcome b))ᴴ := by
                        rw [_root_.LIDT.MIPStarRE.LDT.leftTensor_mul_rightTensor_eq_opTensor]
                  _ = _root_.LIDT.MIPStarRE.LDT.opTensor (A.outcome a * B.outcome b) (R.outcome b) *
                        _root_.LIDT.MIPStarRE.LDT.opTensor ((A.outcome a * B.outcome b)ᴴ) ((R.outcome b)ᴴ) := by
                        rw [_root_.LIDT.MIPStarRE.LDT.conjTranspose_opTensor]
                  _ = _root_.LIDT.MIPStarRE.LDT.opTensor ((A.outcome a * B.outcome b) *
                          ((A.outcome a * B.outcome b)ᴴ))
                        (R.outcome b * (R.outcome b)ᴴ) := by
                        rw [_root_.LIDT.MIPStarRE.LDT.opTensor_mul]
                  _ = _root_.LIDT.MIPStarRE.LDT.opTensor (A.outcome a * (B.outcome b * (B.outcome b * A.outcome a)))
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
    have hbound_terms :
        (∑ b : β,
            _root_.LIDT.MIPStarRE.LDT.opTensor (A.outcome a * (B.outcome b * (B.outcome b * A.outcome a)))
              (R.outcome b)) ≤
          ∑ b : β, _root_.LIDT.MIPStarRE.LDT.opTensor (A.outcome a) (R.outcome b) := by
      refine Finset.sum_le_sum ?_
      intro b _
      apply _root_.LIDT.MIPStarRE.LDT.opTensor_mono_left
      · have hBsq : B.outcome b * B.outcome b ≤ B.outcome b :=
          _root_.LIDT.MIPStarRE.Quantum.sq_le_self (B.outcome_pos b) (B.outcome_le_one b)
        have hleft1 :
            A.outcome a * (B.outcome b * B.outcome b) * A.outcome a ≤
              A.outcome a * B.outcome b * A.outcome a := by
          exact IsSelfAdjoint.conjugate_le_conjugate hBsq (A.outcome_hermitian a)
        have hleft2 :
            A.outcome a * B.outcome b * A.outcome a ≤
              A.outcome a * (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) * A.outcome a := by
          exact IsSelfAdjoint.conjugate_le_conjugate (B.outcome_le_one b) (A.outcome_hermitian a)
        have hleft3 :
            A.outcome a * (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) * A.outcome a ≤
              A.outcome a := by
          simpa using _root_.LIDT.MIPStarRE.Quantum.sq_le_self (A.outcome_pos a) (A.outcome_le_one a)
        calc
          A.outcome a * (B.outcome b * (B.outcome b * A.outcome a))
              = A.outcome a * (B.outcome b * B.outcome b) * A.outcome a := by
                noncomm_ring
          _ ≤ A.outcome a * B.outcome b * A.outcome a := hleft1
          _ ≤ A.outcome a * (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) * A.outcome a := hleft2
          _ ≤ A.outcome a := hleft3
      · exact R.outcome_pos b
    have hsum_right :
        (∑ b : β, _root_.LIDT.MIPStarRE.LDT.opTensor (A.outcome a) (R.outcome b)) =
          _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A.outcome a) := by
      calc
        (∑ b : β, _root_.LIDT.MIPStarRE.LDT.opTensor (A.outcome a) (R.outcome b))
            = ∑ b : β,
                _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A.outcome a) *
                  _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (R.outcome b) := by
              simp [_root_.LIDT.MIPStarRE.LDT.leftTensor_mul_rightTensor_eq_opTensor]
        _ = _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A.outcome a) *
              (∑ b : β, _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (R.outcome b)) := by
              rw [← Matrix.mul_sum]
        _ = _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A.outcome a) *
              _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (∑ b : β, R.outcome b) := by
              rw [_root_.LIDT.MIPStarRE.LDT.rightTensor_finset_sum]
        _ = _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A.outcome a) := by
              rw [R.sum_eq, _root_.LIDT.MIPStarRE.LDT.rightTensor_one]
              simp
    calc
      D a * (D a)ᴴ
          = ∑ b : β,
            _root_.LIDT.MIPStarRE.LDT.opTensor (A.outcome a * (B.outcome b * (B.outcome b * A.outcome a)))
              (R.outcome b) := hrow_expand
      _ ≤ ∑ b : β, _root_.LIDT.MIPStarRE.LDT.opTensor (A.outcome a) (R.outcome b) := hbound_terms
      _ = _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A.outcome a) := hsum_right
  calc
    ∑ a : α,
        (∑ b : β,
          _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A.outcome a * B.outcome b) *
            _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (R.outcome b)) *
        (∑ b : β,
          _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A.outcome a * B.outcome b) *
            _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (R.outcome b))ᴴ
      = ∑ a : α, D a * (D a)ᴴ := by rfl
    _ ≤ ∑ a : α, _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A.outcome a) := by
          exact Finset.sum_le_sum fun a _ => hrow_le a
    _ = _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) A.total := by
          rw [_root_.LIDT.MIPStarRE.LDT.leftTensor_finset_sum, A.sum_eq_total]
    _ ≤ 1 := _root_.LIDT.MIPStarRE.LDT.leftTensor_le_one (ι₂ := ι) A.total_le_one
