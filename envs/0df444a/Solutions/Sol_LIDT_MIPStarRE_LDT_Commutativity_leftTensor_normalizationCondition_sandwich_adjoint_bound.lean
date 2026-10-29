-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Commutativity.leftTensor_normalizationCondition_sandwich_adjoint_bound
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T14:05:52.298409+00:00
-- url     : https://prove2.me/submissions/031f8d9f-4536-4783-adf1-a157835f9885

-- Generated proof for MIPStarRE.LDT.Commutativity.leftTensor_normalizationCondition_sandwich_adjoint_bound.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_EvaluatedSliceBounds_PhaseOneThree
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Products
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Averages
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Transport_Pullback
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Completion
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Local
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_CauchySchwarz
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_CompletionTransfer
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_PolynomialAgreement
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Polynomials
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
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.RingTheory.MvPolynomial.Basic
import Theorems.Thm_LIDT_MIPStarRE_LDT_Commutativity_leftTensor_normalizationCondition_sandwich_bound

open scoped _root_.Matrix

namespace LIDT.MIPStarRE.LDT.Commutativity
end LIDT.MIPStarRE.LDT.Commutativity
namespace LIDT.MIPStarRE.LDT.CommutativityPoints
end LIDT.MIPStarRE.LDT.CommutativityPoints
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries

namespace LIDT

end LIDT

open LIDT
/-!
# Full-slice normalization and self-consistency machinery

Normalization-condition bounds, evaluated projective submeasurements, and
full-slice and evaluated-slice self-consistency estimates used by the scalar-to-tensor
comparison.

The tensor-form estimates are internal to the scalar/tensor comparison recorded
in `docs/decisions/713-scalar-tensor-decision.md`; downstream code should use
the scalar public API exposed by the full-slice transport theorems.

## References

- `references/ldt-paper/commutativity-G.tex`
- `blueprint/src/chapter/ch08_commutativity.tex`
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
    (P : _root_.LIDT.MIPStarRE.LDT.SubMeas α ι) (Q : _root_.LIDT.MIPStarRE.LDT.ProjSubMeas β ι) :
    ∑ a : α,
        (∑ b : β, _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (Q.outcome b * P.outcome a * Q.outcome b))ᴴ *
          (∑ b : β, _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (Q.outcome b * P.outcome a * Q.outcome b)) ≤
      1 := by
  have hbase := _root_.LIDT.MIPStarRE.LDT.Commutativity.leftTensor_normalizationCondition_sandwich_bound (ι := ι) P Q
  have hherm : ∀ a : α,
      (∑ b : β, _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (Q.outcome b * P.outcome a * Q.outcome b))ᴴ =
        ∑ b : β, _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (Q.outcome b * P.outcome a * Q.outcome b) := by
    intro a
    rw [Matrix.conjTranspose_sum]
    apply Finset.sum_congr rfl
    intro b _
    have hP : (P.outcome a)ᴴ = P.outcome a := P.outcome_hermitian a
    have hQ : (Q.outcome b)ᴴ = Q.outcome b := Q.outcome_hermitian b
    have hleftH :
        (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (Q.outcome b * P.outcome a * Q.outcome b))ᴴ =
          _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) ((Q.outcome b * P.outcome a * Q.outcome b)ᴴ) := by
      simpa [_root_.LIDT.MIPStarRE.LDT.leftTensor, _root_.LIDT.MIPStarRE.LDT.opTensor] using
        (_root_.LIDT.MIPStarRE.LDT.conjTranspose_opTensor (ι₁ := ι) (ι₂ := ι)
          (Q.outcome b * P.outcome a * Q.outcome b)
          (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι))
    rw [hleftH]
    simp [Matrix.conjTranspose_mul, hP, hQ, mul_assoc]
  calc
    ∑ a : α,
        (∑ b : β, _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (Q.outcome b * P.outcome a * Q.outcome b))ᴴ *
          (∑ b : β, _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (Q.outcome b * P.outcome a * Q.outcome b))
      = ∑ a : α,
          (∑ b : β, _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (Q.outcome b * P.outcome a * Q.outcome b)) *
            (∑ b : β,
              _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (Q.outcome b * P.outcome a * Q.outcome b))ᴴ := by
          apply Finset.sum_congr rfl
          intro a _
          rw [hherm a]
    _ ≤ 1 := hbase
