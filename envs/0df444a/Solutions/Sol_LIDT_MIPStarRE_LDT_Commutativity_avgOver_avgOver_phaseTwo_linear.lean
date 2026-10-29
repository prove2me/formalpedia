-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Commutativity.avgOver_avgOver_phaseTwo_linear
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T13:57:21.775896+00:00
-- url     : https://prove2.me/submissions/29666b23-5a6d-4df7-9373-f4be05bfe379

-- Generated proof for MIPStarRE.LDT.Commutativity.avgOver_avgOver_phaseTwo_linear.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_SharedHelpers_SharedLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Normalization
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Stability
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_EvaluatedSliceBounds_PhaseOneThree
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_GCommStability_Scalar_First
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Products
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Completion
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Local
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_CauchySchwarz
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SelfConsistency_Extensions
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichMain_Completeness
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_ApproxDelta
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_InnerProduct
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

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.Commutativity
end LIDT.MIPStarRE.LDT.Commutativity
namespace LIDT.MIPStarRE.LDT.Commutativity.GCommStability.Scalar
end LIDT.MIPStarRE.LDT.Commutativity.GCommStability.Scalar
namespace LIDT.MIPStarRE.LDT.CommutativityPoints
end LIDT.MIPStarRE.LDT.CommutativityPoints
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries

namespace LIDT

/- Source helpers from MIPStarRE/LDT/Basic/TensorPlacement.lean. -/
/-!
# Tensor-placement helper lemmas and sandwich tensor estimates

Tensor-sum commutation, positivity/boundedness preservation,
factoring lemmas, and sandwich-residual estimates used in
the main induction step and polynomial-agreement arguments.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT

/-! ### Tensor-placement helper lemmas -/























/-- A complex scalar on the left register factors out of a bipartite tensor product.

This is the tensor-placement version of bilinearity of `opTensor`: placing
`c • A` on the left and multiplying by the right placement of `B` equals the
same scalar multiplying `leftTensor A * rightTensor B`. -/
theorem leftTensor_mul_rightTensor_smul_left
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (c : Error) (A : MIPStarRE.Quantum.Op ι₁) (B : MIPStarRE.Quantum.Op ι₂) :
    leftTensor (ι₂ := ι₂) ((c : ℂ) • A) * rightTensor (ι₁ := ι₁) B =
      (c : ℂ) • (leftTensor (ι₂ := ι₂) A * rightTensor (ι₁ := ι₁) B) := by
  rw [leftTensor_mul_rightTensor_eq_opTensor, leftTensor_mul_rightTensor_eq_opTensor]
  simpa [opTensor] using Matrix.smul_kronecker (c : ℂ) A B

/-- A complex scalar on the right register factors out of a bipartite tensor product.

This is the tensor-placement version of bilinearity of `opTensor`: placing
`c • B` on the right and multiplying by the left placement of `A` equals the
same scalar multiplying `leftTensor A * rightTensor B`. -/
theorem leftTensor_mul_rightTensor_smul_right
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (c : Error) (A : MIPStarRE.Quantum.Op ι₁) (B : MIPStarRE.Quantum.Op ι₂) :
    leftTensor (ι₂ := ι₂) A * rightTensor (ι₁ := ι₁) ((c : ℂ) • B) =
      (c : ℂ) • (leftTensor (ι₂ := ι₂) A * rightTensor (ι₁ := ι₁) B) := by
  rw [leftTensor_mul_rightTensor_eq_opTensor, leftTensor_mul_rightTensor_eq_opTensor]
  simpa [opTensor] using Matrix.kronecker_smul (c : ℂ) A B

/-- A real scalar on the left register factors out of a bipartite tensor product.

This restates `leftTensor_mul_rightTensor_smul_left` for the real scalar action
used by `averageOperatorOverDistribution`, coercing the real scalar to `ℂ` on
the tensor product. -/
theorem leftTensor_mul_rightTensor_real_smul_left
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (c : Error) (A : MIPStarRE.Quantum.Op ι₁) (B : MIPStarRE.Quantum.Op ι₂) :
    leftTensor (ι₂ := ι₂) (c • A) * rightTensor (ι₁ := ι₁) B =
      (c : ℂ) • (leftTensor (ι₂ := ι₂) A * rightTensor (ι₁ := ι₁) B) := by
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  exact leftTensor_mul_rightTensor_smul_left c A B

/-- A real scalar on the right register factors out of a bipartite tensor product.

This restates `leftTensor_mul_rightTensor_smul_right` for the real scalar action
used by `averageOperatorOverDistribution`, coercing the real scalar to `ℂ` on
the tensor product. -/
theorem leftTensor_mul_rightTensor_real_smul_right
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (c : Error) (A : MIPStarRE.Quantum.Op ι₁) (B : MIPStarRE.Quantum.Op ι₂) :
    leftTensor (ι₂ := ι₂) A * rightTensor (ι₁ := ι₁) (c • B) =
      (c : ℂ) • (leftTensor (ι₂ := ι₂) A * rightTensor (ι₁ := ι₁) B) := by
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  exact leftTensor_mul_rightTensor_smul_right c A B











namespace SubMeas



end SubMeas

/-! ### Sandwich tensor estimates -/





end MIPStarRE.LDT

end

end LIDT

open LIDT
/-!
# Phase 2 stability defect infrastructure

Internal helper definitions and lemmas for the Phase 2 scalar bridge in
`ProcessedG`.  These definitions extract and bound the one-dimensional stability
defect controlled by `gCommStability_scalar` (the paper's `clm:g-comm-stability`),
reindex the question-level defect into the stability defect via finite
marginalization, and perform the subtraction algebra that rewrites the phase-2
insertion/removal difference as the negative defect.
-/

@[expose] public section

open LIDT.MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem solution
    {Q V Γ Aidx : Type*} [Fintype Γ] [Fintype Aidx]
    (𝒟Q : _root_.LIDT.MIPStarRE.LDT.Distribution Q) (𝒟V : _root_.LIDT.MIPStarRE.LDT.Distribution V)
    (ψ : _root_.LIDT.MIPStarRE.LDT.QuantumState (ι × ι))
    (F : Q → Γ → Aidx → _root_.LIDT.MIPStarRE.Quantum.Op ι)
    (P : Γ → V → _root_.LIDT.MIPStarRE.Quantum.Op ι)
    (R : _root_.LIDT.MIPStarRE.Quantum.Op ι) :
    _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟V (fun v =>
        _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟Q (fun q =>
          ∑ g : Γ, ∑ a : Aidx,
            _root_.LIDT.MIPStarRE.LDT.ev ψ (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (F q g a * R) *
              _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (P g v)))) =
      ∑ g : Γ,
        _root_.LIDT.MIPStarRE.LDT.ev ψ
          (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
              ((_root_.LIDT.MIPStarRE.LDT.averageOperatorOverDistribution 𝒟Q (fun q => ∑ a : Aidx, F q g a)) * R) *
            _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι)
              (_root_.LIDT.MIPStarRE.LDT.averageOperatorOverDistribution 𝒟V (fun v => P g v))) := by
  classical
  let T : Q → V → Γ → Aidx → _root_.LIDT.MIPStarRE.LDT.Error := fun q v g a =>
    _root_.LIDT.MIPStarRE.LDT.ev ψ (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (F q g a * R) *
      _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (P g v)) * (𝒟Q.weight q * 𝒟V.weight v)
  have hreorder :
      (∑ v ∈ 𝒟V.support, ∑ q ∈ 𝒟Q.support, ∑ g : Γ, ∑ a : Aidx, T q v g a) =
        ∑ g : Γ,
          ∑ v ∈ 𝒟V.support, ∑ q ∈ 𝒟Q.support, ∑ a : Aidx, T q v g a := by
    calc
      (∑ v ∈ 𝒟V.support, ∑ q ∈ 𝒟Q.support, ∑ g : Γ, ∑ a : Aidx, T q v g a)
          = ∑ v ∈ 𝒟V.support,
              ∑ g : Γ, ∑ q ∈ 𝒟Q.support, ∑ a : Aidx, T q v g a := by
            refine Finset.sum_congr rfl ?_
            intro v _
            rw [Finset.sum_comm]
      _ = ∑ g : Γ,
            ∑ v ∈ 𝒟V.support, ∑ q ∈ 𝒟Q.support, ∑ a : Aidx, T q v g a := by
            rw [Finset.sum_comm]
  calc
    _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟V (fun v =>
        _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟Q (fun q =>
          ∑ g : Γ, ∑ a : Aidx,
            _root_.LIDT.MIPStarRE.LDT.ev ψ (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (F q g a * R) *
              _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (P g v))))
        = ∑ v ∈ 𝒟V.support,
            ∑ q ∈ 𝒟Q.support, ∑ g : Γ, ∑ a : Aidx, T q v g a := by
          simp [_root_.LIDT.MIPStarRE.LDT.avgOver, T, Finset.mul_sum, mul_assoc, mul_comm]
    _ = ∑ g : Γ,
          ∑ v ∈ 𝒟V.support, ∑ q ∈ 𝒟Q.support, ∑ a : Aidx, T q v g a := hreorder
    _ = ∑ g : Γ,
        _root_.LIDT.MIPStarRE.LDT.ev ψ
          (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
              ((_root_.LIDT.MIPStarRE.LDT.averageOperatorOverDistribution 𝒟Q (fun q => ∑ a : Aidx, F q g a)) * R) *
            _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι)
              (_root_.LIDT.MIPStarRE.LDT.averageOperatorOverDistribution 𝒟V (fun v => P g v))) := by
          suffices
              ∑ g : Γ, ∑ v ∈ 𝒟V.support, ∑ q ∈ 𝒟Q.support, ∑ a : Aidx,
                  _root_.LIDT.MIPStarRE.LDT.ev ψ (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (F q g a * R) *
                    _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (P g v)) *
                    (𝒟Q.weight q * 𝒟V.weight v) =
                ∑ g : Γ, ∑ v ∈ 𝒟V.support, ∑ q ∈ 𝒟Q.support, ∑ a : Aidx,
                  _root_.LIDT.MIPStarRE.LDT.ev ψ ((𝒟V.weight v : _root_.LIDT.MIPStarRE.LDT.Error) • (𝒟Q.weight q : _root_.LIDT.MIPStarRE.LDT.Error) •
                    (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (F q g a * R) *
                      _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (P g v))) by
            simpa [T, _root_.LIDT.MIPStarRE.LDT.averageOperatorOverDistribution, _root_.LIDT.MIPStarRE.LDT.ev_finset_sum,
              ← _root_.LIDT.MIPStarRE.LDT.leftTensor_finset_sum, ← _root_.LIDT.MIPStarRE.LDT.rightTensor_finset_sum,
              Finset.smul_sum, Finset.sum_mul, Finset.mul_sum,
              _root_.LIDT.MIPStarRE.LDT.leftTensor_mul_rightTensor_real_smul_left,
              _root_.LIDT.MIPStarRE.LDT.leftTensor_mul_rightTensor_real_smul_right] using this
          refine Finset.sum_congr rfl ?_
          intro g _
          refine Finset.sum_congr rfl ?_
          intro v _
          refine Finset.sum_congr rfl ?_
          intro q _
          refine Finset.sum_congr rfl ?_
          intro a _
          let X : _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι) :=
            _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (F q g a * R) * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (P g v)
          change _root_.LIDT.MIPStarRE.LDT.ev ψ X * (𝒟Q.weight q * 𝒟V.weight v) =
            _root_.LIDT.MIPStarRE.LDT.ev ψ ((𝒟V.weight v : _root_.LIDT.MIPStarRE.LDT.Error) • (𝒟Q.weight q : _root_.LIDT.MIPStarRE.LDT.Error) • X)
          rw [_root_.LIDT.MIPStarRE.LDT.ev_real_smul, _root_.LIDT.MIPStarRE.LDT.ev_real_smul]
          ring
