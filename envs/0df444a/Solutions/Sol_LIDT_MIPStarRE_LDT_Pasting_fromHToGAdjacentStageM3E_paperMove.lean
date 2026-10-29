-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Pasting.fromHToGAdjacentStageM3E_paperMove
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T16:09:08.262554+00:00
-- url     : https://prove2.me/submissions/42793eba-b53f-4357-af4f-7e87f678f819

-- Generated proof for MIPStarRE.LDT.Pasting.fromHToGAdjacentStageM3E_paperMove.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionUniformSums
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomialEmbedding
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
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_FromHToG_AdjacentStages_Chain_FinalMove
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_FromHToG_AdjacentStages_Chain_HalfSandwich
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_FromHToG_AdjacentStages_StageA0M1
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_FromHToG_Core_BernoulliTail
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_FromHToG_Core_FactBundles
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_FromHToG_MoveLemmas_Basic
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_FromHToG_PaperBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_Scalar
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_Setup_Definitions
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Families
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Interpolation
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Tuples
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Sandwich_GHatSandwich
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Sandwich_PastedFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Sandwich_Switcheroo
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Statements
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_SwitcherooContraction_ScalarTerms
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_SwitcherooContraction_Split
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_SwitcherooSetup_Centers
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_SwitcherooSetup_Terms
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
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Probability.Distributions.Binomial
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.RingTheory.MvPolynomial.Basic
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_fromHToGAdjacentStageM3_eq_finalLeftShape
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_fromHToGAdjacentStageM4_eq_collapsed
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_fromHToGAdjacentStageM4_eq_finalRightShape
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_fromHToG_SUS_context_avg_le_one
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_fromHToG_closenessOfIP_avgContext
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_fromHToG_selfConsistency_qSDDCore_bound

open scoped _root_.Matrix

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.Commutativity
end LIDT.MIPStarRE.LDT.Commutativity
namespace LIDT.MIPStarRE.LDT.Commutativity.GCommStability.Scalar
end LIDT.MIPStarRE.LDT.Commutativity.GCommStability.Scalar
namespace LIDT.MIPStarRE.LDT.CommutativityPoints
end LIDT.MIPStarRE.LDT.CommutativityPoints
namespace LIDT.MIPStarRE.LDT.Pasting
end LIDT.MIPStarRE.LDT.Pasting
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries

namespace LIDT

/- Source helpers from MIPStarRE/LDT/Pasting/Bernoulli/FromHToG/MoveLemmas/Basic.lean. -/
/-!
# Section 12 pasting: from-H-to-G move lemmas

Tensor, positivity, and Cauchy--Schwarz helper lemmas for the adjacent paper chain.
-/

@[expose] public section

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]































/-- Rewrite a nested finite sum as a sum over a product index. -/
lemma fromHToG_sum_product {α β : Type*} [Fintype α] [Fintype β]
    (F : α → β → Error) :
    (∑ a : α, ∑ b : β, F a b) = ∑ p : α × β, F p.1 p.2 := by
  rw [← Finset.univ_product_univ, Finset.sum_product]











end MIPStarRE.LDT.Pasting

end

/- Source helpers from MIPStarRE/LDT/Pasting/Bernoulli/FromHToG/PaperBounds.lean. -/
/-!
# Section 12 pasting: from-H-to-G collapsed bounds

Collapses the paper endpoint `M₄` to the next Lean stage and records the scalar
bounds used by the final telescope.
-/

@[expose] public section

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]



/-- The collapsed branch expression is exactly the next Lean stage. -/
lemma fromHToGAdjacentStageCollapsed_eq_stage_succ
    (params : Parameters)
    [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (hstageExact : FromHToGAdjacentStageExactFacts params ψbi family)
    (k ℓ : ℕ) :
    fromHToGAdjacentStageCollapsed params ψbi family k ℓ =
      fromHToGStageMass params ψbi family k (ℓ + 1) := by
  classical
  unfold fromHToGAdjacentStageCollapsed fromHToGStageMass
  refine Finset.sum_congr rfl ?_
  intro τ _hτ
  exact (hstageExact.tailWeightRecurrence ℓ τ).symm








end MIPStarRE.LDT.Pasting

end

/- Source helpers from MIPStarRE/LDT/Pasting/Bernoulli/FromHToG/PaperBounds/SandwichContext.lean. -/
/-!
# Section 12 pasting: from-H-to-G S U S context-average bounds

Sandwich-sum identities and the `S U S` context-average bound used in the
second half-sandwich and final move-right Cauchy--Schwarz steps.
-/

@[expose] public section

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The total mass of the tail sandwich family is the identity. -/
lemma fromHToG_gHatSandwichFamily_total_eq_one
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (n : ℕ) (xs : PointTuple params n) :
    (gHatSandwichFamily params family n xs).total = 1 := by
  simp [gHatSandwichFamily, gHatHalfProductTotalOperator_eq_one]

/-- The tail sandwich outcomes sum to the identity. -/
lemma fromHToG_gHatSandwichFamily_sum_eq_one
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (n : ℕ) (xs : PointTuple params n) :
    (∑ gs : GHatTupleOutcome params n,
      (gHatSandwichFamily params family n xs).outcome gs) = 1 := by
  rw [(gHatSandwichFamily params family n xs).sum_eq_total]
  exact fromHToG_gHatSandwichFamily_total_eq_one params family n xs











end MIPStarRE.LDT.Pasting

end

end LIDT

open LIDT
/-!
# Section 12 pasting: from-H-to-G paper moves

This file contains the two analytic moves in the adjacent-stage paper chain:
`M₂ → M₃` and `M₃ → E`.  They are the Cauchy--Schwarz and collapse steps in
`ld-pasting.tex`, immediately before the adjacent-stage recurrence is assembled.
-/

@[expose] public section

open LIDT.MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem solution
    (params : _root_.LIDT.MIPStarRE.LDT.Parameters)
    [_root_.LIDT.MIPStarRE.LDT.FieldModel params.q]
    (ψbi : _root_.LIDT.MIPStarRE.LDT.QuantumState (ι × ι))
    (hnorm : ψbi.IsNormalized)
    (family : _root_.LIDT.MIPStarRE.LDT.IdxPolyFamily params ι)
    (gamma zeta : _root_.LIDT.MIPStarRE.LDT.Error)
    (hfacts : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatFactsStatement params ψbi family gamma zeta)
    (hstageExact : _root_.LIDT.MIPStarRE.LDT.Pasting.FromHToGAdjacentStageExactFacts params ψbi family)
    (k ℓ : ℕ) :
    |_root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGAdjacentStageM3 params ψbi family k ℓ -
        _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGStageMass params ψbi family k (ℓ + 1)| ≤ Real.sqrt (2 * zeta) := by
  let M₃ : _root_.LIDT.MIPStarRE.LDT.Error := _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGAdjacentStageM3 params ψbi family k ℓ
  let M₄ : _root_.LIDT.MIPStarRE.LDT.Error := _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGAdjacentStageM4 params ψbi family k ℓ
  let Collapsed : _root_.LIDT.MIPStarRE.LDT.Error := _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGAdjacentStageCollapsed params ψbi family k ℓ
  let E : _root_.LIDT.MIPStarRE.LDT.Error := _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGStageMass params ψbi family k (ℓ + 1)
  change |M₃ - E| ≤ Real.sqrt (2 * zeta)
  have h₃₄ : |M₃ - M₄| ≤ Real.sqrt (2 * zeta) := by
    let n := k - (ℓ + 1)
    have hM3M4_secondRoot_le :
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params × _root_.LIDT.MIPStarRE.LDT.PointTuple params n)) (fun q =>
          _root_.LIDT.MIPStarRE.LDT.qSDDCore ψbi
            (fun g : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params =>
              _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) ((_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome g))
            (fun g : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params =>
              _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) ((_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome g))) ≤
          2 * zeta := by
      simpa [n] using
        _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToG_selfConsistency_qSDDCore_bound params ψbi family zeta
          hfacts.completedSelfConsistency (n := n)
    let Aop : _root_.LIDT.MIPStarRE.LDT.Fq params × _root_.LIDT.MIPStarRE.LDT.PointTuple params n →
        _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n →
        _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι) := fun q g =>
      _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n q.2 g.2)ᴴ *
        _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) ((_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome g.1)
    let Bop : _root_.LIDT.MIPStarRE.LDT.Fq params × _root_.LIDT.MIPStarRE.LDT.PointTuple params n →
        _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n →
        _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι) := fun q g =>
      _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n q.2 g.2)ᴴ *
        _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) ((_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome g.1)
    let C : _root_.LIDT.MIPStarRE.LDT.Fq params × _root_.LIDT.MIPStarRE.LDT.PointTuple params n →
        _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n → Unit →
        _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι) := fun q ogs _ =>
      let S := _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGRecurrenceWeight params family ℓ
        (_root_.LIDT.MIPStarRE.LDT.Pasting.prependTypeBit ogs.1.isSome (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleType ogs.2))
      let U := (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome ogs.1
      let T := _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n q.2 ogs.2
      _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) T * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (S * U)
    have hM3M4_firstRoot_le_one :
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params × _root_.LIDT.MIPStarRE.LDT.PointTuple params n)) (fun q =>
          ∑ ogs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n,
            let S := _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGRecurrenceWeight params family ℓ
              (_root_.LIDT.MIPStarRE.LDT.Pasting.prependTypeBit ogs.1.isSome (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleType ogs.2))
            let U := (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome ogs.1
            let T := _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n q.2 ogs.2
            _root_.LIDT.MIPStarRE.LDT.ev ψbi
              ((_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) T * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (S * U)) *
                (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) T * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (S * U))ᴴ)) ≤ 1 := by
      exact _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToG_SUS_context_avg_le_one params ψbi hnorm family
        hstageExact.completeBranchAverage hstageExact.incompleteBranchAverage ℓ n
    have hM3M4_secondRoot_pair_le :
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params × _root_.LIDT.MIPStarRE.LDT.PointTuple params n)) (fun q =>
          _root_.LIDT.MIPStarRE.LDT.qSDDCore ψbi (Aop q) (Bop q)) ≤ 2 * zeta := by
      let baseA : _root_.LIDT.MIPStarRE.LDT.Fq params × _root_.LIDT.MIPStarRE.LDT.PointTuple params n → _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params →
          _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι) := fun q g =>
        _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) ((_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome g)
      let baseB : _root_.LIDT.MIPStarRE.LDT.Fq params × _root_.LIDT.MIPStarRE.LDT.PointTuple params n → _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params →
          _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι) := fun q g =>
        _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) ((_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome g)
      let D : _root_.LIDT.MIPStarRE.LDT.Fq params × _root_.LIDT.MIPStarRE.LDT.PointTuple params n → _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params →
          _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n → _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι) := fun q _g gs =>
        _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n q.2 gs)ᴴ
      have hD : ∀ q g,
          ∑ gs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n, (D q g gs)ᴴ * D q g gs ≤ 1 := by
        intro q g
        have hsum :
            (∑ gs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n,
              _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n q.2 gs *
                (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n q.2 gs)ᴴ) =
              (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) := by
          simpa [_root_.LIDT.MIPStarRE.LDT.Pasting.gHatSandwichFamily] using
            _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToG_gHatSandwichFamily_sum_eq_one params family n q.2
        calc
          ∑ gs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n, (D q g gs)ᴴ * D q g gs
            = _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                (∑ gs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n,
                  _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n q.2 gs *
                    (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n q.2 gs)ᴴ) := by
                  dsimp [D]
                  rw [← _root_.LIDT.MIPStarRE.LDT.leftTensor_finset_sum (ι₂ := ι) Finset.univ]
                  refine Finset.sum_congr rfl ?_
                  intro gs _hgs
                  simp [_root_.LIDT.MIPStarRE.LDT.leftTensor_mul_leftTensor]
          _ = 1 := by simp [hsum, _root_.LIDT.MIPStarRE.LDT.leftTensor]
          _ ≤ 1 := le_rfl
      have hcab := _root_.LIDT.MIPStarRE.LDT.Preliminaries.cabApproxDelta ψbi
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params × _root_.LIDT.MIPStarRE.LDT.PointTuple params n))
        baseA baseB D (2 * zeta) (by simpa [baseA, baseB] using hM3M4_secondRoot_le) hD
      simpa [Aop, Bop, baseA, baseB, D] using hcab
    have hM3M4_cauchySchwarz := _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToG_closenessOfIP_avgContext ψbi hnorm
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params × _root_.LIDT.MIPStarRE.LDT.PointTuple params n))
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution_weight_sum_le_one (_root_.LIDT.MIPStarRE.LDT.Fq params × _root_.LIDT.MIPStarRE.LDT.PointTuple params n))
      Aop Bop C (2 * zeta) hM3M4_secondRoot_pair_le
      (by simpa [C] using hM3M4_firstRoot_le_one)
    let L : _root_.LIDT.MIPStarRE.LDT.Error := _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params × _root_.LIDT.MIPStarRE.LDT.PointTuple params n)) fun q =>
      ∑ ogs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n,
        ∑ u : Unit, _root_.LIDT.MIPStarRE.LDT.ev ψbi (C q ogs u * Aop q ogs)
    let R : _root_.LIDT.MIPStarRE.LDT.Error := _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params × _root_.LIDT.MIPStarRE.LDT.PointTuple params n)) fun q =>
      ∑ ogs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n,
        ∑ u : Unit, _root_.LIDT.MIPStarRE.LDT.ev ψbi (C q ogs u * Bop q ogs)
    have hcsLR : |L - R| ≤ Real.sqrt (2 * zeta) := by
      exact hM3M4_cauchySchwarz
    have hM₃_shape : M₃ =
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params × _root_.LIDT.MIPStarRE.LDT.PointTuple params n)) fun q =>
          ∑ g : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params, ∑ gs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n,
            let S := _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGRecurrenceWeight params family ℓ
              (_root_.LIDT.MIPStarRE.LDT.Pasting.prependTypeBit g.isSome (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleType gs))
            let U := (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome g
            let T := _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n q.2 gs
            _root_.LIDT.MIPStarRE.LDT.ev ψbi ((_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (T * Tᴴ) * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (S * U)) *
              _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) U) := by
      simpa [M₃, n] using _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGAdjacentStageM3_eq_finalLeftShape params ψbi family k ℓ
    have hM₄_shape : M₄ =
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params × _root_.LIDT.MIPStarRE.LDT.PointTuple params n)) fun q =>
          ∑ g : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params, ∑ gs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n,
            let S := _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGRecurrenceWeight params family ℓ
              (_root_.LIDT.MIPStarRE.LDT.Pasting.prependTypeBit g.isSome (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleType gs))
            let U := (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome g
            let T := _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n q.2 gs
            _root_.LIDT.MIPStarRE.LDT.ev ψbi ((_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (T * Tᴴ) * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (S * U)) *
              _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) U) := by
      simpa [M₄, n] using _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGAdjacentStageM4_eq_finalRightShape params ψbi family k ℓ
    have hM₃_L : M₃ = L := by
      rw [hM₃_shape]
      refine _root_.LIDT.MIPStarRE.LDT.avgOver_congr _ _ _ ?_
      intro q
      rw [_root_.LIDT.MIPStarRE.LDT.Pasting.fromHToG_sum_product]
      refine Finset.sum_congr rfl ?_
      intro ogs _hogs
      simp only [Aop, C, Finset.univ_unique, Finset.sum_singleton]
      congr 1
      simp [_root_.LIDT.MIPStarRE.LDT.opTensor_mul, mul_assoc]
    have hM₄_R : M₄ = R := by
      rw [hM₄_shape]
      refine _root_.LIDT.MIPStarRE.LDT.avgOver_congr _ _ _ ?_
      intro q
      rw [_root_.LIDT.MIPStarRE.LDT.Pasting.fromHToG_sum_product]
      refine Finset.sum_congr rfl ?_
      intro ogs _hogs
      simp only [Bop, C, Finset.univ_unique, Finset.sum_singleton]
      congr 1
      simp [_root_.LIDT.MIPStarRE.LDT.opTensor_mul, mul_assoc]
    simpa [hM₃_L, hM₄_R] using hcsLR
  have h₄collapsed : M₄ = Collapsed := by
    simpa [M₄, Collapsed] using
      _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGAdjacentStageM4_eq_collapsed params ψbi family
        hstageExact.completeBranchAverage hstageExact.incompleteBranchAverage k ℓ
  have hcollapsedE : Collapsed = E := by
    calc
      Collapsed = _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGStageMass params ψbi family k (ℓ + 1) := by
            simpa [Collapsed] using
              _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGAdjacentStageCollapsed_eq_stage_succ
                params ψbi family hstageExact k ℓ
      _ = E := rfl
  have h₄E : M₄ = E := h₄collapsed.trans hcollapsedE
  /- Paper lines 1648--1661.  After the analytic move `M₃ → M₄`, collapse the
  head projector using projectivity, average the complete/incomplete head
  branches, and finally apply `eq:S-recurrence` to reach the next Lean stage. -/
  simpa [h₄E] using h₃₄
