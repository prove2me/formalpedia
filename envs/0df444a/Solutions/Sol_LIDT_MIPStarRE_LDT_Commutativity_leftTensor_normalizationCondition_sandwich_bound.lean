-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Commutativity.leftTensor_normalizationCondition_sandwich_bound
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T14:00:31.983149+00:00
-- url     : https://prove2.me/submissions/729411b3-6989-406c-96eb-baafc56e5944

-- Generated proof for MIPStarRE.LDT.Commutativity.leftTensor_normalizationCondition_sandwich_bound.
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

open scoped _root_.Matrix

namespace LIDT.MIPStarRE.LDT.Commutativity
end LIDT.MIPStarRE.LDT.Commutativity
namespace LIDT.MIPStarRE.LDT.CommutativityPoints
end LIDT.MIPStarRE.LDT.CommutativityPoints
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries

namespace LIDT

/- Source helpers from MIPStarRE/LDT/Commutativity/Transport/FullSlice/Machinery/Normalization.lean. -/
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

namespace MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Paper `lem:normalization-condition` (`commutativity-G.tex` line 309).

For a sub-measurement `P` and projective sub-measurement `Q`, the sandwiched
family `C_{a,b} = Q_b · P_a · Q_b` satisfies the `closenessOfIP` normalization
condition `∑_a (∑_b C_{a,b}) (∑_b C_{a,b})ᴴ ≤ I`. -/
lemma normalizationCondition_sandwich_bound
    {α β : Type*} [Fintype α] [Fintype β]
    (P : SubMeas α ι) (Q : ProjSubMeas β ι) :
    ∑ a : α,
        (∑ b : β, Q.outcome b * P.outcome a * Q.outcome b) *
          (∑ b : β, Q.outcome b * P.outcome a * Q.outcome b)ᴴ ≤ 1 := by
  simpa [normalizationConditionSquareOperator,
    normalizationConditionSquareFamily,
    normalizationConditionSandwichedTotalOperator,
    normalizationConditionSandwichedTotalFamily,
    normalizationConditionSandwichedFamily,
    normalizationConditionSandwichedOperator,
    postprocess] using
    (normalizationConditionSquareFamily P Q).total_le_one















end MIPStarRE.LDT.Commutativity

end

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
        (∑ b : β, _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (Q.outcome b * P.outcome a * Q.outcome b)) *
          (∑ b : β, _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (Q.outcome b * P.outcome a * Q.outcome b))ᴴ ≤
      1 := by
  let T : α → _root_.LIDT.MIPStarRE.Quantum.Op ι := fun a =>
    ∑ b : β, Q.outcome b * P.outcome a * Q.outcome b
  calc
    ∑ a : α,
        (∑ b : β, _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (Q.outcome b * P.outcome a * Q.outcome b)) *
          (∑ b : β, _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (Q.outcome b * P.outcome a * Q.outcome b))ᴴ
      = ∑ a : α, _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (T a * (T a)ᴴ) := by
          refine Finset.sum_congr rfl ?_
          intro a _
          have hsum :
              (∑ b : β,
                  _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (Q.outcome b * P.outcome a * Q.outcome b)) =
                _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (T a) := by
            simp [T, _root_.LIDT.MIPStarRE.LDT.leftTensor_finset_sum]
          rw [hsum]
          have hleft_adj :
              (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (T a))ᴴ = _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) ((T a)ᴴ) := by
            simpa [_root_.LIDT.MIPStarRE.LDT.leftTensor, _root_.LIDT.MIPStarRE.LDT.opTensor] using
              (_root_.LIDT.MIPStarRE.LDT.conjTranspose_opTensor (ι₁ := ι) (ι₂ := ι)
                (T a) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι))
          rw [hleft_adj, _root_.LIDT.MIPStarRE.LDT.leftTensor_mul_leftTensor]
    _ = _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (∑ a : α, T a * (T a)ᴴ) := by
          rw [← _root_.LIDT.MIPStarRE.LDT.leftTensor_finset_sum (ι₂ := ι) Finset.univ (fun a => T a * (T a)ᴴ)]
    _ ≤ 1 := by
          exact _root_.LIDT.MIPStarRE.LDT.leftTensor_le_one (ι₂ := ι) <| by
            simpa [T] using _root_.LIDT.MIPStarRE.LDT.Commutativity.normalizationCondition_sandwich_bound P Q
