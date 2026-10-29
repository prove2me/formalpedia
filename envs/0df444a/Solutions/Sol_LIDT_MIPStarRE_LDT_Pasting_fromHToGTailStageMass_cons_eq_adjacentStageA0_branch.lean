-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Pasting.fromHToGTailStageMass_cons_eq_adjacentStageA0_branch
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T15:58:31.477301+00:00
-- url     : https://prove2.me/submissions/13d9423f-7f7e-4620-9a3b-67cce0695e56

-- Generated proof for MIPStarRE.LDT.Pasting.fromHToGTailStageMass_cons_eq_adjacentStageA0_branch.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_FromHToG_Core_BernoulliTail
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_FromHToG_Core_FactBundles
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_FromHToG_MoveLemmas_Basic
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
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_fromHToG_avgOver_tail_type_ev
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_fromHToG_cons_type_outcome_sum

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

/- Source helpers from MIPStarRE/LDT/Pasting/Bernoulli/FromHToG/MoveLemmas/TailStage.lean. -/
/-!
# Section 12 pasting: from-H-to-G head-tail stage reindexing

The head-tail reindexing lemmas for the adjacent-stage source expression in the
paper's `from H to G` chain.
-/

@[expose] public section

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]







/-- Fold a tail point/outcome average written directly with the sandwich-family
outcomes into `averagedSandwichByTypeSubMeas`. -/
lemma fromHToG_avgOver_tail_type_ev_sandwich
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι) (n : ℕ) (τ : GHatType n)
    (B : MIPStarRE.Quantum.Op ι) :
    avgOver (uniformDistribution (PointTuple params n)) (fun xs =>
      ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
          gHatTupleType gs = τ,
        ev ψbi (leftTensor (ι₂ := ι)
          ((gHatSandwichFamily params family n xs).outcome gs) *
            rightTensor (ι₁ := ι) B)) =
      ev ψbi (leftTensor (ι₂ := ι)
        (averagedSandwichByTypeSubMeas params family n τ).total *
          rightTensor (ι₁ := ι) B) := by
  simpa [gHatSandwichFamily] using
    (fromHToG_avgOver_tail_type_ev params ψbi family n τ B)



end MIPStarRE.LDT.Pasting

end

end LIDT

open LIDT
/-!
# Section 12 pasting: from-H-to-G head-tail stage reindexing

The head-tail reindexing lemmas for the adjacent-stage source expression in the
paper's `from H to G` chain.
-/

@[expose] public section

open LIDT.MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem solution
    (params : _root_.LIDT.MIPStarRE.LDT.Parameters) [_root_.LIDT.MIPStarRE.LDT.FieldModel params.q]
    (ψbi : _root_.LIDT.MIPStarRE.LDT.QuantumState (ι × ι))
    (family : _root_.LIDT.MIPStarRE.LDT.IdxPolyFamily params ι)
    (ℓ n : ℕ) (b : Bool) (τ : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatType n) :
    _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGTailStageMass params ψbi family ℓ (_root_.LIDT.MIPStarRE.LDT.Pasting.prependTypeBit b τ) =
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params)) fun x =>
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.PointTuple params n)) fun xs =>
          ∑ g ∈ (Finset.univ : Finset (_root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params)) with g.isSome = b,
            ∑ gs ∈ (Finset.univ : Finset (_root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n)) with
                _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleType gs = τ,
              let S := _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGRecurrenceWeight params family ℓ (_root_.LIDT.MIPStarRE.LDT.Pasting.prependTypeBit b τ)
              let U := (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family x).outcome g
              let T := _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n xs gs
              _root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (U * T * Tᴴ * U) *
                _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) S) := by
  classical
  let S := _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGRecurrenceWeight params family ℓ (_root_.LIDT.MIPStarRE.LDT.Pasting.prependTypeBit b τ)
  let F : _root_.LIDT.MIPStarRE.LDT.Fq params → _root_.LIDT.MIPStarRE.LDT.PointTuple params n → _root_.LIDT.MIPStarRE.LDT.Error := fun x xs =>
    ∑ g ∈ (Finset.univ : Finset (_root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params)) with g.isSome = b,
      ∑ gs ∈ (Finset.univ : Finset (_root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n)) with
          _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleType gs = τ,
        let U := (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family x).outcome g
        let T := _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n xs gs
        _root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (U * T * Tᴴ * U) * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) S)
  calc
    _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGTailStageMass params ψbi family ℓ (_root_.LIDT.MIPStarRE.LDT.Pasting.prependTypeBit b τ)
        = _root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
            (_root_.LIDT.MIPStarRE.LDT.Pasting.averagedSandwichByTypeSubMeas params family (n + 1)
              (_root_.LIDT.MIPStarRE.LDT.Pasting.prependTypeBit b τ)).total * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) S) := by
            unfold _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGTailStageMass _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGTailStageFamily
            rfl
    _ = _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.PointTuple params (n + 1))) (fun xs' =>
          ∑ gs' ∈ (Finset.univ : Finset (_root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params (n + 1))) with
              _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleType gs' = _root_.LIDT.MIPStarRE.LDT.Pasting.prependTypeBit b τ,
            _root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
              ((_root_.LIDT.MIPStarRE.LDT.Pasting.gHatSandwichFamily params family (n + 1) xs').outcome gs') *
                _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) S)) := by
            exact (_root_.LIDT.MIPStarRE.LDT.Pasting.fromHToG_avgOver_tail_type_ev_sandwich params ψbi family
              (n + 1) (_root_.LIDT.MIPStarRE.LDT.Pasting.prependTypeBit b τ) S).symm
    _ = _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params × _root_.LIDT.MIPStarRE.LDT.PointTuple params n)) (fun q =>
          ∑ gs' ∈ (Finset.univ : Finset (_root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params (n + 1))) with
              _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleType gs' = _root_.LIDT.MIPStarRE.LDT.Pasting.prependTypeBit b τ,
            _root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
              ((_root_.LIDT.MIPStarRE.LDT.Pasting.gHatSandwichFamily params family (n + 1)
                ((_root_.LIDT.MIPStarRE.LDT.Pasting.pointTupleConsEquiv params n).symm q)).outcome gs') *
                _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) S)) := by
            exact _root_.LIDT.MIPStarRE.LDT.avgOver_uniform_equiv (_root_.LIDT.MIPStarRE.LDT.Pasting.pointTupleConsEquiv params n) _
    _ = _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params × _root_.LIDT.MIPStarRE.LDT.PointTuple params n)) (fun q =>
          F q.1 q.2) := by
            refine _root_.LIDT.MIPStarRE.LDT.avgOver_congr _ _ _ ?_
            intro q
            rcases q with ⟨x, xs⟩
            simpa [F, S, _root_.LIDT.MIPStarRE.LDT.Pasting.pointTupleConsEquiv] using
              (_root_.LIDT.MIPStarRE.LDT.Pasting.fromHToG_cons_type_outcome_sum params ψbi family b τ x xs S)
    _ = _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params)) (fun x =>
          _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.PointTuple params n)) (fun xs => F x xs)) := by
            exact _root_.LIDT.MIPStarRE.LDT.avgOver_uniform_prod (α := _root_.LIDT.MIPStarRE.LDT.Fq params) (β := _root_.LIDT.MIPStarRE.LDT.PointTuple params n) (f := F)
