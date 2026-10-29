-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Commutativity.fullSlice_closenessOfIP_CAB_hEval_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T14:25:03.13649+00:00
-- url     : https://prove2.me/submissions/002940ff-f75e-4ee1-a730-c87b749f7d5a

-- Generated proof for MIPStarRE.LDT.Commutativity.fullSlice_closenessOfIP_CAB_hEval_sqrt.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Main_Auxiliary_HEvalTransport
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Products
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Averages
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Machinery_Marginalization_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Machinery_Marginalization_Y
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Machinery_Normalization
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
import Theorems.Thm_LIDT_MIPStarRE_LDT_Commutativity_evaluatedSliceCommutation_of_evaluationSpecialization
import Theorems.Thm_LIDT_MIPStarRE_LDT_Commutativity_evaluatedSliceCommutation_qSDDOp_avg_eq

open scoped _root_.Matrix

namespace LIDT.MIPStarRE.LDT.Commutativity
end LIDT.MIPStarRE.LDT.Commutativity
namespace LIDT.MIPStarRE.LDT.CommutativityPoints
end LIDT.MIPStarRE.LDT.CommutativityPoints
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries

namespace LIDT

/- Source helpers from MIPStarRE/LDT/Commutativity/Main/Auxiliary/HEvalTransport.lean. -/
/-!
# Section 11 commutativity: hEval/closenessOfIP transport

Evaluated-side closeness-of-IP transport and strong `hEval` bounds
(`eq:evaluate-gcom-at-points` through `eq:don't-understand-the-numbering-system`).

Provides the evaluated-side `closenessOfIP` chain on `CAB` products,
including zero-operator triangulation helpers and the sharp bound
`fullSlice_closenessOfIP_CAB_hEval_sqrt` and its paper-envelope estimate
`fullSlice_closenessOfIP_CAB_hEval`.

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



private lemma evaluatedSliceProductLeft_qSDDOp_zero_le_one
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (hnorm : strategy.state.IsNormalized)
    (q : EvaluatedSliceQuestion params) :
    qSDDOp strategy.state
      (evaluatedSliceProductLeft params strategy family q)
      (zeroEvaluatedSliceOpFamily (ι := ι) params) ≤ 1 := by
  let A : SubMeas (Fq params) ι := evaluatedSliceFirstFactor params family q
  let B : SubMeas (Fq params) ι := evaluatedSliceSecondFactor params family q
  let S := sandwichByOuterSubMeas B A
  unfold qSDDOp qSDDCore evaluatedSliceProductLeft leftOrderedProductOpFamily
  calc
    ∑ ab : EvaluatedSliceOutcome params,
        ev strategy.state
          (((leftTensor (ι₂ := ι) (A.outcome ab.1 * B.outcome ab.2) - 0)ᴴ) *
            (leftTensor (ι₂ := ι) (A.outcome ab.1 * B.outcome ab.2) - 0))
      = ∑ ab : EvaluatedSliceOutcome params,
          ev strategy.state
            (leftTensor (ι₂ := ι)
              (B.outcome ab.2 * A.outcome ab.1 * B.outcome ab.2)) := by
          refine Finset.sum_congr rfl ?_
          intro ab _
          rcases ab with ⟨a, b⟩
          have hAherm : (A.outcome a)ᴴ = A.outcome a := A.outcome_hermitian a
          have hBherm : (B.outcome b)ᴴ = B.outcome b := B.outcome_hermitian b
          have hAproj : A.outcome a * A.outcome a = A.outcome a := by
            simpa [A, evaluatedSliceFirstFactor] using
              evaluatedPointFamily_outcome_proj params family q.1 a
          have hleftH :
              (leftTensor (ι₂ := ι) (A.outcome a * B.outcome b))ᴴ =
                leftTensor (ι₂ := ι) ((A.outcome a * B.outcome b)ᴴ) := by
            simp
          have hmul :
              (((A.outcome a * B.outcome b)ᴴ) *
                (A.outcome a * B.outcome b)) =
              B.outcome b * A.outcome a * B.outcome b := by
            calc
              (((A.outcome a * B.outcome b)ᴴ) *
                  (A.outcome a * B.outcome b))
                = (((B.outcome b)ᴴ * (A.outcome a)ᴴ) *
                    (A.outcome a * B.outcome b)) := by
                    simp [Matrix.conjTranspose_mul]
              _ = B.outcome b * (A.outcome a * A.outcome a) * B.outcome b := by
                    simp [hAherm, hBherm, mul_assoc]
              _ = B.outcome b * A.outcome a * B.outcome b := by
                    simp [hAproj, mul_assoc]
          calc
            ev strategy.state
                (((leftTensor (ι₂ := ι) (A.outcome a * B.outcome b) - 0)ᴴ) *
                  (leftTensor (ι₂ := ι) (A.outcome a * B.outcome b) - 0))
              = ev strategy.state
                  (((leftTensor (ι₂ := ι) (A.outcome a * B.outcome b))ᴴ) *
                    leftTensor (ι₂ := ι) (A.outcome a * B.outcome b)) := by simp
            _ = ev strategy.state
                  (leftTensor (ι₂ := ι)
                    (((A.outcome a * B.outcome b)ᴴ) *
                      (A.outcome a * B.outcome b))) := by
                    rw [hleftH, leftTensor_mul_leftTensor]
            _ = ev strategy.state
                  (leftTensor (ι₂ := ι)
                    (B.outcome b * A.outcome a * B.outcome b)) := by rw [hmul]
    _ = ev strategy.state (leftTensor (ι₂ := ι) S.total) := by
          rw [← ev_sum strategy.state
            (fun ab : EvaluatedSliceOutcome params =>
              leftTensor (ι₂ := ι) (B.outcome ab.2 * A.outcome ab.1 * B.outcome ab.2))]
          congr 1
          calc
            ∑ ab : EvaluatedSliceOutcome params,
                leftTensor (ι₂ := ι) (B.outcome ab.2 * A.outcome ab.1 * B.outcome ab.2)
              = leftTensor (ι₂ := ι)
                  (∑ ab : EvaluatedSliceOutcome params,
                    B.outcome ab.2 * A.outcome ab.1 * B.outcome ab.2) := by
                    exact leftTensor_finset_sum (ι₂ := ι) Finset.univ
                      (fun ab : EvaluatedSliceOutcome params =>
                        B.outcome ab.2 * A.outcome ab.1 * B.outcome ab.2)
            _ = leftTensor (ι₂ := ι) S.total := by
                    congr 1
                    calc
                      ∑ ab : EvaluatedSliceOutcome params,
                          B.outcome ab.2 * A.outcome ab.1 * B.outcome ab.2
                        = ∑ ba : Fq params × Fq params,
                            B.outcome ba.1 * A.outcome ba.2 * B.outcome ba.1 := by
                              exact Fintype.sum_equiv
                                (Equiv.prodComm (Fq params) (Fq params))
                                (fun ab : Fq params × Fq params =>
                                  B.outcome ab.2 * A.outcome ab.1 * B.outcome ab.2)
                                (fun ba : Fq params × Fq params =>
                                  B.outcome ba.1 * A.outcome ba.2 * B.outcome ba.1)
                                (by intro ab; simp)
                      _ = S.total := by
                            simpa [S, sandwichByOuterSubMeas] using S.sum_eq_total
    _ ≤ ev strategy.state (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
          exact ev_mono strategy.state _ _ <|
            leftTensor_le_one (ι₂ := ι) S.total_le_one
    _ = 1 := ev_one_of_isNormalized strategy.state hnorm

private lemma zero_qSDDOp_evaluatedSliceProductRight_le_one
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (hnorm : strategy.state.IsNormalized)
    (q : EvaluatedSliceQuestion params) :
    qSDDOp strategy.state
      (zeroEvaluatedSliceOpFamily (ι := ι) params)
      (evaluatedSliceProductRight params strategy family q) ≤ 1 := by
  let A : SubMeas (Fq params) ι := evaluatedSliceFirstFactor params family q
  let B : SubMeas (Fq params) ι := evaluatedSliceSecondFactor params family q
  let S := sandwichByOuterSubMeas A B
  unfold qSDDOp qSDDCore evaluatedSliceProductRight
  calc
    ∑ ab : EvaluatedSliceOutcome params,
        ev strategy.state
          (((0 - leftTensor (ι₂ := ι) (B.outcome ab.2 * A.outcome ab.1))ᴴ) *
            (0 - leftTensor (ι₂ := ι) (B.outcome ab.2 * A.outcome ab.1)))
      = ∑ ab : EvaluatedSliceOutcome params,
          ev strategy.state
            (leftTensor (ι₂ := ι)
              (A.outcome ab.1 * B.outcome ab.2 * A.outcome ab.1)) := by
          refine Finset.sum_congr rfl ?_
          intro ab _
          rcases ab with ⟨a, b⟩
          have hAherm : (A.outcome a)ᴴ = A.outcome a := A.outcome_hermitian a
          have hBherm : (B.outcome b)ᴴ = B.outcome b := B.outcome_hermitian b
          have hBproj : B.outcome b * B.outcome b = B.outcome b := by
            simpa [B, evaluatedSliceSecondFactor] using
              evaluatedPointFamily_outcome_proj params family q.2 b
          have hleftH :
              (leftTensor (ι₂ := ι) (B.outcome b * A.outcome a))ᴴ =
                leftTensor (ι₂ := ι) ((B.outcome b * A.outcome a)ᴴ) := by
            simp
          have hmul :
              (((B.outcome b * A.outcome a)ᴴ) *
                (B.outcome b * A.outcome a)) =
              A.outcome a * B.outcome b * A.outcome a := by
            calc
              (((B.outcome b * A.outcome a)ᴴ) *
                  (B.outcome b * A.outcome a))
                = (((A.outcome a)ᴴ * (B.outcome b)ᴴ) *
                    (B.outcome b * A.outcome a)) := by
                    simp [Matrix.conjTranspose_mul]
              _ = A.outcome a * (B.outcome b * B.outcome b) * A.outcome a := by
                    simp [hAherm, hBherm, mul_assoc]
              _ = A.outcome a * B.outcome b * A.outcome a := by
                    simp [hBproj, mul_assoc]
          calc
            ev strategy.state
                (((0 - leftTensor (ι₂ := ι) (B.outcome b * A.outcome a))ᴴ) *
                  (0 - leftTensor (ι₂ := ι) (B.outcome b * A.outcome a)))
              = ev strategy.state
                  (((leftTensor (ι₂ := ι) (B.outcome b * A.outcome a))ᴴ) *
                    leftTensor (ι₂ := ι) (B.outcome b * A.outcome a)) := by simp
            _ = ev strategy.state
                  (leftTensor (ι₂ := ι)
                    (((B.outcome b * A.outcome a)ᴴ) *
                      (B.outcome b * A.outcome a))) := by
                    rw [hleftH, leftTensor_mul_leftTensor]
            _ = ev strategy.state
                  (leftTensor (ι₂ := ι)
                    (A.outcome a * B.outcome b * A.outcome a)) := by rw [hmul]
    _ = ev strategy.state (leftTensor (ι₂ := ι) S.total) := by
          rw [← ev_sum strategy.state
            (fun ab : EvaluatedSliceOutcome params =>
              leftTensor (ι₂ := ι) (A.outcome ab.1 * B.outcome ab.2 * A.outcome ab.1))]
          congr 1
          calc
            ∑ ab : EvaluatedSliceOutcome params,
                leftTensor (ι₂ := ι) (A.outcome ab.1 * B.outcome ab.2 * A.outcome ab.1)
              = leftTensor (ι₂ := ι)
                  (∑ ab : EvaluatedSliceOutcome params,
                    A.outcome ab.1 * B.outcome ab.2 * A.outcome ab.1) := by
                    exact leftTensor_finset_sum (ι₂ := ι) Finset.univ
                      (fun ab : EvaluatedSliceOutcome params =>
                        A.outcome ab.1 * B.outcome ab.2 * A.outcome ab.1)
            _ = leftTensor (ι₂ := ι) S.total := by
                    congr 1
                    simpa [S, sandwichByOuterSubMeas] using S.sum_eq_total
    _ ≤ ev strategy.state (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
          exact ev_mono strategy.state _ _ <|
            leftTensor_le_one (ι₂ := ι) S.total_le_one
    _ = 1 := ev_one_of_isNormalized strategy.state hnorm






end MIPStarRE.LDT.Commutativity

end

/- Source helpers from MIPStarRE/LDT/Preliminaries/DistanceBounds.lean. -/
/-!
# Preliminary comparison theorems: distance bounds

Triangle-inequality style bounds for `SDDRel` and `SDDOpRel`.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT

/-! ### Infrastructure: triangle inequality for `SDDRel` -/















/-! ### Infrastructure: triangle inequality for `SDDOpRel` -/

/-- The operator-family squared-distance defect is nonnegative. -/
theorem qSDDOp_nonneg
    {Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι] [Fintype Outcome]
    (ψ : QuantumState ι) (A B : OpFamily Outcome ι) :
    0 ≤ qSDDOp ψ A B := by
  unfold qSDDOp qSDDCore
  exact Finset.sum_nonneg fun a _ => ev_adjoint_self_nonneg ψ _












end MIPStarRE.LDT.Preliminaries

end

end LIDT

open LIDT
/-!
# Section 11 commutativity: hEval/closenessOfIP transport

Evaluated-side closeness-of-IP transport and strong `hEval` bounds
(`eq:evaluate-gcom-at-points` through `eq:don't-understand-the-numbering-system`).

Provides the evaluated-side `closenessOfIP` chain on `CAB` products,
including zero-operator triangulation helpers and the sharp bound
`fullSlice_closenessOfIP_CAB_hEval_sqrt` and its paper-envelope estimate
`fullSlice_closenessOfIP_CAB_hEval`.

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
    (params : _root_.LIDT.MIPStarRE.LDT.Parameters) [_root_.LIDT.MIPStarRE.LDT.FieldModel params.q]
    (strategy : _root_.LIDT.MIPStarRE.LDT.SymStrat params.next ι) (family : _root_.LIDT.MIPStarRE.LDT.IdxPolyFamily params ι)
    (gamma zeta : _root_.LIDT.MIPStarRE.LDT.Error)
    (hnorm : strategy.state.IsNormalized)
    (hEval :
      _root_.LIDT.MIPStarRE.LDT.SDDOpRel strategy.state
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params))
        (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedFromFullSliceProductLeft params strategy family)
        (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedFromFullSliceProductRight params strategy family)
        (_root_.LIDT.MIPStarRE.LDT.Commutativity.commDataProcessedGError params gamma zeta)) :
    |_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceABAAvg params strategy family -
        _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceABABAvg params strategy family| ≤
      Real.sqrt (_root_.LIDT.MIPStarRE.LDT.Commutativity.commDataProcessedGError params gamma zeta) := by
  let δ := _root_.LIDT.MIPStarRE.LDT.Commutativity.commDataProcessedGError params gamma zeta
  let d : _root_.LIDT.MIPStarRE.LDT.Error :=
    _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceABAAvg params strategy family -
      _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceABABAvg params strategy family
  have hEval' :=
    _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceCommutation_of_evaluationSpecialization
      params strategy family δ hEval
  have hδ :
      _root_.LIDT.MIPStarRE.LDT.sddErrorOp strategy.state
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params))
        (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceProductLeft params strategy family)
        (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceProductRight params strategy family) ≤ δ :=
    hEval'.squaredDistanceBound
  have h4 :
      _root_.LIDT.MIPStarRE.LDT.sddErrorOp strategy.state
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params))
        (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceProductLeft params strategy family)
        (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceProductRight params strategy family) ≤ 4 := by
    have hleft : _root_.LIDT.MIPStarRE.LDT.SDDOpRel strategy.state
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params))
        (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceProductLeft params strategy family)
        (fun _ => zeroEvaluatedSliceOpFamily (ι := ι) params)
        1 := by
      constructor
      unfold _root_.LIDT.MIPStarRE.LDT.sddErrorOp
      exact _root_.LIDT.MIPStarRE.LDT.avgOver_uniform_le_const
        (fun q =>
          _root_.LIDT.MIPStarRE.LDT.qSDDOp strategy.state
            (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceProductLeft params strategy family q)
            (zeroEvaluatedSliceOpFamily (ι := ι) params))
        1
        (fun q =>
          evaluatedSliceProductLeft_qSDDOp_zero_le_one params strategy family hnorm q)
    have hright : _root_.LIDT.MIPStarRE.LDT.SDDOpRel strategy.state
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params))
        (fun _ => zeroEvaluatedSliceOpFamily (ι := ι) params)
        (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceProductRight params strategy family)
        1 := by
      constructor
      unfold _root_.LIDT.MIPStarRE.LDT.sddErrorOp
      exact _root_.LIDT.MIPStarRE.LDT.avgOver_uniform_le_const
        (fun q =>
          _root_.LIDT.MIPStarRE.LDT.qSDDOp strategy.state
            (zeroEvaluatedSliceOpFamily (ι := ι) params)
            (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceProductRight params strategy family q))
        1
        (fun q =>
          zero_qSDDOp_evaluatedSliceProductRight_le_one params strategy family hnorm q)
    have htri :=
      _root_.LIDT.MIPStarRE.LDT.Preliminaries.stateDependentDistanceOpRel_triangle
        strategy.state
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params))
        (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceProductLeft params strategy family)
        (fun _ => zeroEvaluatedSliceOpFamily (ι := ι) params)
        (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceProductRight params strategy family)
        1 1 hleft hright
    linarith [htri.squaredDistanceBound]
  have hExpand :=
    _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceCommutation_qSDDOp_avg_eq params strategy family
  have hd_nonneg : 0 ≤ d := by
    have hsdd_nonneg :
        0 ≤ _root_.LIDT.MIPStarRE.LDT.sddErrorOp strategy.state
          (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params))
          (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceProductLeft params strategy family)
          (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceProductRight params strategy family) := by
      unfold _root_.LIDT.MIPStarRE.LDT.sddErrorOp
      exact _root_.LIDT.MIPStarRE.LDT.avgOver_nonneg (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params)) _
        (fun q => _root_.LIDT.MIPStarRE.LDT.Preliminaries.qSDDOp_nonneg strategy.state _ _)
    rw [hExpand] at hsdd_nonneg
    simpa [d, _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceABAAvg, _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceABABAvg] using hsdd_nonneg
  have hδ' : 2 * d ≤ δ := by
    rw [hExpand] at hδ
    simpa [d, _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceABAAvg, _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceABABAvg] using hδ
  have h4' : 2 * d ≤ 4 := by
    rw [hExpand] at h4
    simpa [d, _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceABAAvg, _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceABABAvg] using h4
  have hδ_nonneg : 0 ≤ δ := by
    linarith [hδ', hd_nonneg]
  have hd_le_sqrt : d ≤ Real.sqrt δ := by
    by_cases hδ4 : δ ≤ 4
    · have hd_half : d ≤ δ / 2 := by
        linarith [hδ']
      have hhalf_le : δ / 2 ≤ Real.sqrt δ := by
        have hsqrt_nonneg : 0 ≤ Real.sqrt δ := Real.sqrt_nonneg _
        nlinarith [Real.sq_sqrt hδ_nonneg, hδ4, hsqrt_nonneg]
      exact hd_half.trans hhalf_le
    · have h4le : 4 ≤ δ := le_of_lt (lt_of_not_ge hδ4)
      have hd_two : d ≤ 2 := by
        linarith [h4']
      have htwo_le : 2 ≤ Real.sqrt δ := by
        have hsqrt : Real.sqrt (4 : _root_.LIDT.MIPStarRE.LDT.Error) ≤ Real.sqrt δ :=
          Real.sqrt_le_sqrt h4le
        norm_num at hsqrt
        exact hsqrt
      exact hd_two.trans htwo_le
  calc
    |_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceABAAvg params strategy family -
        _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceABABAvg params strategy family|
      = d := by
          dsimp [d]
          exact abs_of_nonneg hd_nonneg
    _ ≤ Real.sqrt δ := hd_le_sqrt
    _ = Real.sqrt (_root_.LIDT.MIPStarRE.LDT.Commutativity.commDataProcessedGError params gamma zeta) := by
          rfl
