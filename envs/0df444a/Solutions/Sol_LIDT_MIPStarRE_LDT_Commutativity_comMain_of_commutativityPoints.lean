-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Commutativity.comMain_of_commutativityPoints
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T17:47:16.432133+00:00
-- url     : https://prove2.me/submissions/1a4ed15d-a757-4662-a335-1b4db2192d47

-- Generated proof for MIPStarRE.LDT.Commutativity.comMain_of_commutativityPoints.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_GCommStability_Scalar_RawSecond
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Main_Auxiliary_HEvalTransport
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Main_Auxiliary_ScalarMarginalization
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Products
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_PaperChainPhaseFive
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_ProcessedG_MainChain
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_ProcessedG_PhaseTwo
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
import Theorems.Thm_LIDT_MIPStarRE_LDT_Commutativity_commDataProcessedG_of_commutativityPoints
import Theorems.Thm_LIDT_MIPStarRE_LDT_Commutativity_fullSliceCommutation_of_evaluated_on_evaluated_questions

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

/- Source helpers from MIPStarRE/LDT/Commutativity/Transport/EvaluationSpecialization.lean. -/
/-!
# Section 11 commutativity: transport via evaluation specialization

Postprocessing identities for `leftPlacedOpFamily` of bilinear products, used
to transport bounds across evaluation specializations of the full-slice
commutation argument.

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
/-- Postprocessing a `leftPlacedOpFamily` of a bilinear product equals
the `leftPlacedOpFamily` of the product of postprocessed submeasurements,
for any binary operation `g` that factors over finite sums. -/
private lemma postprocess_leftPlacedOpFamily_product_outcome
    {α₁ α₂ β₁ β₂ : Type*}
    [Fintype α₁] [Fintype α₂] [Fintype β₁] [Fintype β₂]
    (A : SubMeas α₁ ι) (B : SubMeas α₂ ι)
    (f₁ : α₁ → β₁) (f₂ : α₂ → β₂) (b₁ : β₁) (b₂ : β₂)
    (g : MIPStarRE.Quantum.Op ι → MIPStarRE.Quantum.Op ι →
      MIPStarRE.Quantum.Op ι)
    (hg_factor : ∀ (S : Finset α₁) (T : Finset α₂)
      (fA : α₁ → MIPStarRE.Quantum.Op ι)
      (fB : α₂ → MIPStarRE.Quantum.Op ι),
      ∑ a ∈ S ×ˢ T, g (fA a.1) (fB a.2) =
        g (∑ a ∈ S, fA a) (∑ b ∈ T, fB b)) :
    (OpFamily.postprocess
      (OpFamily.leftPlacedOpFamily (ιB := ι)
        (⟨fun ab => g (A.outcome ab.1) (B.outcome ab.2),
          g A.total B.total⟩ : OpFamily (α₁ × α₂) ι))
      (fun ab => (f₁ ab.1, f₂ ab.2))).outcome (b₁, b₂) =
    (OpFamily.leftPlacedOpFamily (ιB := ι)
      (⟨fun ab => g ((postprocess A f₁).outcome ab.1)
          ((postprocess B f₂).outcome ab.2),
        g (postprocess A f₁).total
          (postprocess B f₂).total⟩ :
          OpFamily (β₁ × β₂) ι)).outcome (b₁, b₂) := by
  classical
  simp only [OpFamily.postprocess, OpFamily.leftPlacedOpFamily,
    postprocess]
  rw [leftTensor_finset_sum (ι₂ := ι)]
  congr 1
  set S := Finset.univ.filter (fun a₁ => f₁ a₁ = b₁)
  set T := Finset.univ.filter (fun a₂ => f₂ a₂ = b₂)
  trans ∑ a ∈ S ×ˢ T, g (A.outcome a.1) (B.outcome a.2)
  · apply Finset.sum_congr
    · ext ⟨x, y⟩; simp [S, T, Prod.mk.injEq]
    · intros; rfl
  · exact hg_factor S T A.outcome B.outcome

/-- The evaluated-from-full-slice ordered product equals the
evaluated-slice ordered product at each question-outcome pair. -/
private lemma evaluatedFromFullSliceProductLeft_outcome_eq
    (params : Parameters) [FieldModel params.q] (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (q : EvaluatedSliceQuestion params)
    (ab : EvaluatedSliceOutcome params) :
    (evaluatedFromFullSliceProductLeft
      params strategy family q).outcome ab =
    (evaluatedSliceProductLeft
      params strategy family q).outcome ab := by
  obtain ⟨a, b⟩ := ab
  unfold evaluatedFromFullSliceProductLeft evaluatedSliceProductLeft
    fullSliceProductLeft leftOrderedProductOpFamily
    evaluateFullSliceOutcomeAtQuestion
    fullSliceQuestionOfEvaluatedSlice
    orderedProductOpFamily
  exact
    postprocess_leftPlacedOpFamily_product_outcome
      (fullSliceFirstFactor params family
        (pointHeight params q.1, pointHeight params q.2))
      (fullSliceSecondFactor params family
        (pointHeight params q.1, pointHeight params q.2))
      (fun g => g (truncatePoint params q.1))
      (fun h => h (truncatePoint params q.2)) a b (· * ·) fun S T fA fB => by
      rw [Finset.sum_product]
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul]

/-- The evaluated-from-full-slice reversed product equals the
evaluated-slice reversed product at each question-outcome pair. -/
private lemma evaluatedFromFullSliceProductRight_outcome_eq
    (params : Parameters) [FieldModel params.q] (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (q : EvaluatedSliceQuestion params)
    (ab : EvaluatedSliceOutcome params) :
    (evaluatedFromFullSliceProductRight
      params strategy family q).outcome ab =
    (evaluatedSliceProductRight
      params strategy family q).outcome ab := by
  obtain ⟨a, b⟩ := ab
  unfold evaluatedFromFullSliceProductRight
    evaluatedSliceProductRight fullSliceProductRight
    evaluateFullSliceOutcomeAtQuestion
    fullSliceQuestionOfEvaluatedSlice
    reversedProductOpFamily
  exact
    postprocess_leftPlacedOpFamily_product_outcome
      (fullSliceFirstFactor params family
        (pointHeight params q.1, pointHeight params q.2))
      (fullSliceSecondFactor params family
        (pointHeight params q.1, pointHeight params q.2))
      (fun g => g (truncatePoint params q.1))
      (fun h => h (truncatePoint params q.2)) a b (fun x y => y * x) fun S T fA fB => by
      rw [Finset.sum_product]
      simp_rw [← Finset.sum_mul]
      rw [← Finset.mul_sum]

/-- The evaluated-from-full-slice SDD error equals the evaluated-slice
SDD error, because the postprocessed product equals the product of
postprocessed submeasurements at every question-outcome pair. -/
lemma evaluationSpecialization_sddErrorOp_eq
    (params : Parameters) [FieldModel params.q] (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) :
    sddErrorOp strategy.state
      (uniformDistribution (EvaluatedSliceQuestion params))
      (evaluatedFromFullSliceProductLeft
        params strategy family)
      (evaluatedFromFullSliceProductRight
        params strategy family) =
    sddErrorOp strategy.state
      (uniformDistribution (EvaluatedSliceQuestion params))
      (evaluatedSliceProductLeft params strategy family)
      (evaluatedSliceProductRight
        params strategy family) := by
  simp only [sddErrorOp, qSDDOp, qSDDCore]
  simp_rw [evaluatedFromFullSliceProductLeft_outcome_eq,
      evaluatedFromFullSliceProductRight_outcome_eq]



end MIPStarRE.LDT.Commutativity

end

/- Source helpers from MIPStarRE/LDT/Commutativity/Transport/Pullback.lean. -/
/-!
# Section 11 commutativity: evaluated-slice pullback

Pullback equivalence reindexing evaluated-slice questions into their truncated
points and the underlying full-slice question, used to transport full-slice
bounds.

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


/-- Pulling a family on `FullSliceQuestion` back along
`fullSliceQuestionOfEvaluatedSlice` preserves the averaged `sddErrorOp`. -/
lemma sddErrorOp_pullback_fullSliceQuestion_eq
    (params : Parameters) [FieldModel params.q]
    (ψ : QuantumState (ι × ι))
    {Outcome : Type*} [Fintype Outcome]
    (A B : IdxOpFamily (FullSliceQuestion params) Outcome (ι × ι)) :
    sddErrorOp ψ
      (uniformDistribution (EvaluatedSliceQuestion params))
      (fun q => A (fullSliceQuestionOfEvaluatedSlice params q))
      (fun q => B (fullSliceQuestionOfEvaluatedSlice params q)) =
    sddErrorOp ψ
      (uniformDistribution (FullSliceQuestion params))
      A B := by
  let e := evaluatedSliceQuestionEquiv params
  unfold sddErrorOp
  simpa [e, evaluatedSliceQuestionEquiv, fullSliceQuestionOfEvaluatedSlice] using
    (avgOver_uniform_equiv_snd (e := e)
      (f := fun xy : FullSliceQuestion params => qSDDOp ψ (A xy) (B xy)))

/-- Any `SDDOpRel` bound proved after pulling back along
`fullSliceQuestionOfEvaluatedSlice` descends to `FullSliceQuestion`. -/
lemma sddOpRel_of_pullback_fullSliceQuestion
    (params : Parameters) [FieldModel params.q]
    (ψ : QuantumState (ι × ι))
    {Outcome : Type*} [Fintype Outcome]
    (A B : IdxOpFamily (FullSliceQuestion params) Outcome (ι × ι))
    (δ : Error) :
    SDDOpRel ψ
      (uniformDistribution (EvaluatedSliceQuestion params))
      (fun q => A (fullSliceQuestionOfEvaluatedSlice params q))
      (fun q => B (fullSliceQuestionOfEvaluatedSlice params q))
      δ →
    SDDOpRel ψ
      (uniformDistribution (FullSliceQuestion params))
      A B
      δ := by
  intro ⟨h⟩
  constructor
  rw [← sddErrorOp_pullback_fullSliceQuestion_eq params ψ A B]
  exact h


end MIPStarRE.LDT.Commutativity

end

end LIDT

open LIDT
/-!
# Section 11 commutativity: final results

Top-level `thm:com-main` statement, lifting evaluated commutation back to
full-slice commutation via the two-step Schwartz–Zippel marginalization.

The two-step lift uses a hybrid scalar/tensor architecture (Option 3):
the public conclusion is an `SDDOpRel` on operator families, composed from
scalar transport lemmas whose proofs internally use tensor-form intermediates
for the PSD Schwartz–Zippel argument.
See `docs/decisions/713-scalar-tensor-decision.md`.

## References

- `references/ldt-paper/commutativity-points.tex`
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
    (params : _root_.LIDT.MIPStarRE.LDT.Parameters)
    [_root_.LIDT.MIPStarRE.LDT.FieldModel params.q]
    (strategy : _root_.LIDT.MIPStarRE.LDT.SymStrat params.next ι)
    (gamma zeta : _root_.LIDT.MIPStarRE.LDT.Error)
    (hnorm : strategy.state.IsNormalized)
    (hcomm :
      _root_.LIDT.MIPStarRE.LDT.SDDOpRel strategy.state
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.GlobalVariance.PointPairQuestion params.next))
        (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.pointMeasurementProductLeft params.next strategy)
        (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.pointMeasurementProductRight params.next strategy)
        (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.commutativityPointsError params.next gamma))
    (hgamma_nonneg : 0 ≤ gamma)
    (family : _root_.LIDT.MIPStarRE.LDT.IdxPolyFamily params ι)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : _root_.LIDT.MIPStarRE.LDT.IdxPolyFamily.SliceBoundednessInput strategy family zeta) :
    _root_.LIDT.MIPStarRE.LDT.Commutativity.ComMainConclusion params strategy family gamma zeta := by
  let hEval :=
    _root_.LIDT.MIPStarRE.LDT.Commutativity.commDataProcessedG_of_commutativityPoints
      params strategy gamma zeta hnorm hcomm hgamma_nonneg family hcons hself hbound
  have hSpecialized :
      _root_.LIDT.MIPStarRE.LDT.SDDOpRel strategy.state
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params))
        (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedFromFullSliceProductLeft params strategy family)
        (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedFromFullSliceProductRight params strategy family)
        (_root_.LIDT.MIPStarRE.LDT.Commutativity.commDataProcessedGError params gamma zeta) := by
    constructor
    rw [_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluationSpecialization_sddErrorOp_eq]
    exact hEval.squaredDistanceBound
  have hzeta_nonneg : 0 ≤ zeta :=
    le_trans (_root_.LIDT.MIPStarRE.LDT.sddError_nonneg _ _ _ _)
      hself.sliceSelfConsistency.squaredDistanceBound
  exact
    _root_.LIDT.MIPStarRE.LDT.Commutativity.sddOpRel_of_pullback_fullSliceQuestion params strategy.state
      (_root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceProductLeft params strategy family)
      (_root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceProductRight params strategy family)
      (_root_.LIDT.MIPStarRE.LDT.Commutativity.comMainError params gamma zeta)
      (_root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceCommutation_of_evaluated_on_evaluated_questions
        params strategy family gamma zeta
        hnorm hgamma_nonneg hzeta_nonneg hself hSpecialized)
