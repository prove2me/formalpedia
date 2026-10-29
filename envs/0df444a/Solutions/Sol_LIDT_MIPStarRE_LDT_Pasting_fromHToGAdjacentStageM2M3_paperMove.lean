-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Pasting.fromHToGAdjacentStageM2M3_paperMove
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T16:20:58.499921+00:00
-- url     : https://prove2.me/submissions/d2afe5e6-9ba0-41c0-b91c-4198761215c4

-- Generated proof for MIPStarRE.LDT.Pasting.fromHToGAdjacentStageM2M3_paperMove.
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
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_fromHToGAdjacentStageM2_eq_halfSandwichRightAdjointLeftActionShape
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_fromHToGAdjacentStageM3_eq_halfSandwichLeftAdjointLeftActionShape
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_fromHToG_SUS_context_avg_le_one
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_fromHToG_closenessOfIP_avgContext
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_fromHToG_headTail_adjoint_qSDDCore_bound

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
    (hgamma_nonneg : 0 ≤ gamma) (hzeta_nonneg : 0 ≤ zeta)
    (hhalf : ∀ j : ℕ, 2 ≤ j →
      _root_.LIDT.MIPStarRE.LDT.Pasting.CommuteGHalfSandwichStatement params ψbi family gamma zeta j)
    (hstageExact : _root_.LIDT.MIPStarRE.LDT.Pasting.FromHToGAdjacentStageExactFacts params ψbi family)
    (k ℓ : ℕ) :
    |_root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGAdjacentStageM2 params ψbi family k ℓ -
        _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGAdjacentStageM3 params ψbi family k ℓ| ≤
      Real.sqrt (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwichError params gamma zeta k) := by
  let M₂ : _root_.LIDT.MIPStarRE.LDT.Error := _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGAdjacentStageM2 params ψbi family k ℓ
  let M₃ : _root_.LIDT.MIPStarRE.LDT.Error := _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGAdjacentStageM3 params ψbi family k ℓ
  change |M₂ - M₃| ≤ Real.sqrt (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwichError params gamma zeta k)
  /- Paper lines 1551--1610.  This is the second half-sandwich commutation:
  rewrite `eq:commute-g-part-one` into the source/target forms of
  `eq:commute-g-part-two`, then split `eq:call-again-later-part-dos` into its
  two square-root estimates.  The first root uses `eq:S-sandwich`; the second
  root is identified with the first root from `eq:call-this-later`. -/
  let n := k - (ℓ + 1)
  by_cases hn0 : n = 0
  · have hM₂ : M₂ =
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params × _root_.LIDT.MIPStarRE.LDT.PointTuple params n)) fun q =>
          ∑ g : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params, ∑ gs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n,
            let S := _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGRecurrenceWeight params family ℓ
              (_root_.LIDT.MIPStarRE.LDT.Pasting.prependTypeBit g.isSome (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleType gs))
            let U := (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome g
            let T := _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n q.2 gs
            _root_.LIDT.MIPStarRE.LDT.ev ψbi ((_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) T * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (S * U)) *
              _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (U * Tᴴ)) := by
      exact _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGAdjacentStageM2_eq_halfSandwichRightAdjointLeftActionShape
        params ψbi family k ℓ
    have hM₃ : M₃ =
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params × _root_.LIDT.MIPStarRE.LDT.PointTuple params n)) fun q =>
          ∑ g : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params, ∑ gs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n,
            let S := _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGRecurrenceWeight params family ℓ
              (_root_.LIDT.MIPStarRE.LDT.Pasting.prependTypeBit g.isSome (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleType gs))
            let U := (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome g
            let T := _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n q.2 gs
            _root_.LIDT.MIPStarRE.LDT.ev ψbi ((_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) T * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (S * U)) *
              _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (Tᴴ * U)) := by
      exact _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGAdjacentStageM3_eq_halfSandwichLeftAdjointLeftActionShape
        params ψbi family k ℓ
    have hM : M₂ = M₃ := by
      rw [hM₂, hM₃]
      rw [hn0]
      simp [_root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator]
    rw [hM, sub_self, abs_zero]
    exact Real.sqrt_nonneg _
  · have hnpos : 1 ≤ n := Nat.pos_iff_ne_zero.mpr hn0
    have hn : 2 ≤ n + 1 := Nat.succ_le_succ hnpos
    have hnk : n + 1 ≤ k := by
      dsimp [n]
      omega
    have hM₂_source : M₂ =
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params × _root_.LIDT.MIPStarRE.LDT.PointTuple params n)) fun q =>
          ∑ g : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params, ∑ gs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n,
            let S := _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGRecurrenceWeight params family ℓ
              (_root_.LIDT.MIPStarRE.LDT.Pasting.prependTypeBit g.isSome (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleType gs))
            let U := (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome g
            let T := _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n q.2 gs
            _root_.LIDT.MIPStarRE.LDT.ev ψbi ((_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) T * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (S * U)) *
              _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (U * Tᴴ)) := by
      simpa only [M₂] using
        _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGAdjacentStageM2_eq_halfSandwichRightAdjointLeftActionShape
          params ψbi family k ℓ
    have hM₃_target : M₃ =
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params × _root_.LIDT.MIPStarRE.LDT.PointTuple params n)) fun q =>
          ∑ g : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params, ∑ gs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n,
            let S := _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGRecurrenceWeight params family ℓ
              (_root_.LIDT.MIPStarRE.LDT.Pasting.prependTypeBit g.isSome (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleType gs))
            let U := (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome g
            let T := _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n q.2 gs
            _root_.LIDT.MIPStarRE.LDT.ev ψbi ((_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) T * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (S * U)) *
              _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (Tᴴ * U)) := by
      simpa only [M₃] using
        _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGAdjacentStageM3_eq_halfSandwichLeftAdjointLeftActionShape
          params ψbi family k ℓ
    have h₂₃_secondRoot_le_nu4 :
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params × _root_.LIDT.MIPStarRE.LDT.PointTuple params n)) (fun q =>
          _root_.LIDT.MIPStarRE.LDT.qSDDCore ψbi
            (fun ogs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n =>
              _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                ((_root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n q.2 ogs.2)ᴴ *
                  (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome ogs.1))
            (fun ogs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n =>
              _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                ((_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome ogs.1 *
                  (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n q.2 ogs.2)ᴴ))) ≤
          _root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwichError params gamma zeta k := by
      simpa [n] using
        _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToG_headTail_adjoint_qSDDCore_bound params ψbi family gamma zeta
          hgamma_nonneg hzeta_nonneg hhalf (n := n) (k := k) hn hnk
    have h₂₃_firstRoot_le_one :
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params × _root_.LIDT.MIPStarRE.LDT.PointTuple params n)) (fun q =>
          ∑ ogs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n,
            let S := _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGRecurrenceWeight params family ℓ
              (_root_.LIDT.MIPStarRE.LDT.Pasting.prependTypeBit ogs.1.isSome (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleType ogs.2))
            let U := (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome ogs.1
            let T := _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n q.2 ogs.2
            _root_.LIDT.MIPStarRE.LDT.ev ψbi
              ((_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) T * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (S * U)) *
                (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) T * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (S * U))ᴴ)) ≤ 1 := by
      exact @_root_.LIDT.MIPStarRE.LDT.Pasting.fromHToG_SUS_context_avg_le_one _ _ _ params _ ψbi hnorm family
        hstageExact.completeBranchAverage hstageExact.incompleteBranchAverage ℓ n
    have h₂₃_cauchySchwarz :
        |M₂ - M₃| ≤ Real.sqrt (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwichError params gamma zeta k) := by
      let Aop : _root_.LIDT.MIPStarRE.LDT.Fq params × _root_.LIDT.MIPStarRE.LDT.PointTuple params n →
          _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n →
          _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι) := fun q ogs =>
        _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
          ((_root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n q.2 ogs.2)ᴴ *
            (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome ogs.1)
      let Bop : _root_.LIDT.MIPStarRE.LDT.Fq params × _root_.LIDT.MIPStarRE.LDT.PointTuple params n →
          _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n →
          _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι) := fun q ogs =>
        _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
          ((_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome ogs.1 *
            (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n q.2 ogs.2)ᴴ)
      let Cop : _root_.LIDT.MIPStarRE.LDT.Fq params × _root_.LIDT.MIPStarRE.LDT.PointTuple params n →
          _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n → Unit →
          _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι) := fun q ogs _ =>
        let S := _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGRecurrenceWeight params family ℓ
          (_root_.LIDT.MIPStarRE.LDT.Pasting.prependTypeBit ogs.1.isSome (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleType ogs.2))
        let U := (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome ogs.1
        let T := _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n q.2 ogs.2
        _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) T * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (S * U)
      have hcs := _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToG_closenessOfIP_avgContext ψbi hnorm
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params × _root_.LIDT.MIPStarRE.LDT.PointTuple params n))
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution_weight_sum_le_one (_root_.LIDT.MIPStarRE.LDT.Fq params × _root_.LIDT.MIPStarRE.LDT.PointTuple params n))
        Aop Bop Cop (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwichError params gamma zeta k)
        (by simpa [Aop, Bop] using h₂₃_secondRoot_le_nu4)
        (by simpa [Cop] using h₂₃_firstRoot_le_one)
      have hM₂_prod : M₂ =
          _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params × _root_.LIDT.MIPStarRE.LDT.PointTuple params n)) fun q =>
            ∑ ogs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n,
              let S := _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGRecurrenceWeight params family ℓ
                (_root_.LIDT.MIPStarRE.LDT.Pasting.prependTypeBit ogs.1.isSome (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleType ogs.2))
              let U := (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome ogs.1
              let T := _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n q.2 ogs.2
              _root_.LIDT.MIPStarRE.LDT.ev ψbi ((_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) T * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (S * U)) *
                _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (U * Tᴴ)) := by
        rw [hM₂_source]
        refine _root_.LIDT.MIPStarRE.LDT.avgOver_congr _ _ _ ?_
        intro q
        exact _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToG_sum_product (fun g gs =>
          let S := _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGRecurrenceWeight params family ℓ
            (_root_.LIDT.MIPStarRE.LDT.Pasting.prependTypeBit g.isSome (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleType gs))
          let U := (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome g
          let T := _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n q.2 gs
          _root_.LIDT.MIPStarRE.LDT.ev ψbi ((_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) T * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (S * U)) *
            _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (U * Tᴴ)))
      have hM₃_prod : M₃ =
          _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params × _root_.LIDT.MIPStarRE.LDT.PointTuple params n)) fun q =>
            ∑ ogs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n,
              let S := _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGRecurrenceWeight params family ℓ
                (_root_.LIDT.MIPStarRE.LDT.Pasting.prependTypeBit ogs.1.isSome (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleType ogs.2))
              let U := (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome ogs.1
              let T := _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n q.2 ogs.2
              _root_.LIDT.MIPStarRE.LDT.ev ψbi ((_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) T * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (S * U)) *
                _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (Tᴴ * U)) := by
        rw [hM₃_target]
        refine _root_.LIDT.MIPStarRE.LDT.avgOver_congr _ _ _ ?_
        intro q
        exact _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToG_sum_product (fun g gs =>
          let S := _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGRecurrenceWeight params family ℓ
            (_root_.LIDT.MIPStarRE.LDT.Pasting.prependTypeBit g.isSome (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleType gs))
          let U := (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome g
          let T := _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n q.2 gs
          _root_.LIDT.MIPStarRE.LDT.ev ψbi ((_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) T * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (S * U)) *
            _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (Tᴴ * U)))
      let L : _root_.LIDT.MIPStarRE.LDT.Error := _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params × _root_.LIDT.MIPStarRE.LDT.PointTuple params n)) fun q =>
        ∑ ogs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n,
          ∑ u : Unit, _root_.LIDT.MIPStarRE.LDT.ev ψbi (Cop q ogs u * Aop q ogs)
      let R : _root_.LIDT.MIPStarRE.LDT.Error := _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params × _root_.LIDT.MIPStarRE.LDT.PointTuple params n)) fun q =>
        ∑ ogs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n,
          ∑ u : Unit, _root_.LIDT.MIPStarRE.LDT.ev ψbi (Cop q ogs u * Bop q ogs)
      have hcsLR : |L - R| ≤ Real.sqrt (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwichError params gamma zeta k) := by
        exact hcs
      have hM₂_R : M₂ = R := by
        rw [hM₂_prod]
        simp only [R, Bop, Cop, Finset.univ_unique, Finset.sum_singleton]
      have hM₃_L : M₃ = L := by
        rw [hM₃_prod]
        simp only [L, Aop, Cop, Finset.univ_unique, Finset.sum_singleton]
      calc
        |M₂ - M₃| = |R - L| := by rw [hM₂_R, hM₃_L]
        _ = |L - R| := abs_sub_comm R L
        _ ≤ Real.sqrt (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwichError params gamma zeta k) := hcsLR
    exact h₂₃_cauchySchwarz
