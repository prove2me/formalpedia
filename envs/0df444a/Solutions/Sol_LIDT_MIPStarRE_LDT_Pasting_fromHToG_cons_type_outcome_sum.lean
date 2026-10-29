-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Pasting.fromHToG_cons_type_outcome_sum
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T15:47:37.620746+00:00
-- url     : https://prove2.me/submissions/0fb5bf36-97e9-4a0d-9ade-e54a6f1340b5

-- Generated proof for MIPStarRE.LDT.Pasting.fromHToG_cons_type_outcome_sum.
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
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_fromHToG_gHatSandwichFamily_cons_outcome
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_fromHToG_gHatTupleType_cons_eq

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
    (family : _root_.LIDT.MIPStarRE.LDT.IdxPolyFamily params ι) {n : ℕ}
    (b : Bool) (τ : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatType n) (x : _root_.LIDT.MIPStarRE.LDT.Fq params) (xs : _root_.LIDT.MIPStarRE.LDT.PointTuple params n)
    (S : _root_.LIDT.MIPStarRE.Quantum.Op ι) :
    (∑ gs' ∈ (Finset.univ : Finset (_root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params (n + 1))) with
        _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleType gs' = _root_.LIDT.MIPStarRE.LDT.Pasting.prependTypeBit b τ,
      _root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
        ((_root_.LIDT.MIPStarRE.LDT.Pasting.gHatSandwichFamily params family (n + 1) (Fin.cons x xs)).outcome gs') *
          _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) S)) =
      ∑ g ∈ (Finset.univ : Finset (_root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params)) with g.isSome = b,
        ∑ gs ∈ (Finset.univ : Finset (_root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n)) with
            _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleType gs = τ,
          let U := (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family x).outcome g
          let T := _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n xs gs
          _root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (U * T * Tᴴ * U) * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) S) := by
  classical
  simp only [Finset.sum_filter]
  calc
    (∑ gs' : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params (n + 1),
      if _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleType gs' = _root_.LIDT.MIPStarRE.LDT.Pasting.prependTypeBit b τ then
        _root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
          ((_root_.LIDT.MIPStarRE.LDT.Pasting.gHatSandwichFamily params family (n + 1) (Fin.cons x xs)).outcome gs') *
            _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) S)
      else 0)
      = ∑ p : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n,
          if _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleType (Fin.cons p.1 p.2) = _root_.LIDT.MIPStarRE.LDT.Pasting.prependTypeBit b τ then
            _root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
              ((_root_.LIDT.MIPStarRE.LDT.Pasting.gHatSandwichFamily params family (n + 1) (Fin.cons x xs)).outcome
                (Fin.cons p.1 p.2)) * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) S)
          else 0 := by
          exact Fintype.sum_equiv (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleOutcomeConsEquiv' params n)
            (fun gs' : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params (n + 1) =>
              if _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleType gs' = _root_.LIDT.MIPStarRE.LDT.Pasting.prependTypeBit b τ then
                _root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                  ((_root_.LIDT.MIPStarRE.LDT.Pasting.gHatSandwichFamily params family (n + 1) (Fin.cons x xs)).outcome gs') *
                    _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) S)
              else 0)
            (fun p : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n =>
              if _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleType (Fin.cons p.1 p.2) = _root_.LIDT.MIPStarRE.LDT.Pasting.prependTypeBit b τ then
                _root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                  ((_root_.LIDT.MIPStarRE.LDT.Pasting.gHatSandwichFamily params family (n + 1) (Fin.cons x xs)).outcome
                    (Fin.cons p.1 p.2)) * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) S)
              else 0)
            (by
              intro gs'
              have hcons : Fin.cons (gs' 0) (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleOutcomeTail gs') = gs' := by
                funext i
                cases i using Fin.cases with
                | zero => rfl
                | succ j => rfl
              change
                (if _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleType gs' = _root_.LIDT.MIPStarRE.LDT.Pasting.prependTypeBit b τ then
                  _root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                    ((_root_.LIDT.MIPStarRE.LDT.Pasting.gHatSandwichFamily params family (n + 1) (Fin.cons x xs)).outcome gs') *
                      _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) S)
                else 0) =
                if _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleType (Fin.cons (gs' 0) (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleOutcomeTail gs')) =
                    _root_.LIDT.MIPStarRE.LDT.Pasting.prependTypeBit b τ then
                  _root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                    ((_root_.LIDT.MIPStarRE.LDT.Pasting.gHatSandwichFamily params family (n + 1) (Fin.cons x xs)).outcome
                      (Fin.cons (gs' 0) (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleOutcomeTail gs'))) * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) S)
                else 0
              rw [hcons])
    _ = ∑ p : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n,
          if p.1.isSome = b ∧ _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleType p.2 = τ then
            let U := (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family x).outcome p.1
            let T := _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n xs p.2
            _root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (U * T * Tᴴ * U) * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) S)
          else 0 := by
          refine Finset.sum_congr rfl ?_
          intro p _hp
          by_cases hp : p.1.isSome = b ∧ _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleType p.2 = τ
          · have htype : _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleType (Fin.cons p.1 p.2) = _root_.LIDT.MIPStarRE.LDT.Pasting.prependTypeBit b τ :=
              (_root_.LIDT.MIPStarRE.LDT.Pasting.fromHToG_gHatTupleType_cons_eq params b τ p.1 p.2).2 hp
            rw [if_pos htype, if_pos hp]
            simp [_root_.LIDT.MIPStarRE.LDT.Pasting.fromHToG_gHatSandwichFamily_cons_outcome]
          · rw [if_neg]
            · rw [if_neg hp]
            · intro h
              exact hp ((_root_.LIDT.MIPStarRE.LDT.Pasting.fromHToG_gHatTupleType_cons_eq params b τ p.1 p.2).1 h)
    _ = ∑ g : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params,
          ∑ gs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n,
            if g.isSome = b ∧ _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleType gs = τ then
              let U := (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family x).outcome g
              let T := _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n xs gs
              _root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (U * T * Tᴴ * U) * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) S)
            else 0 := by
          rw [← Finset.univ_product_univ, Finset.sum_product]
    _ = ∑ g : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params,
          if g.isSome = b then
            ∑ gs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n,
              if _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleType gs = τ then
                let U := (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family x).outcome g
                let T := _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n xs gs
                _root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (U * T * Tᴴ * U) * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) S)
              else 0
          else 0 := by
          refine Finset.sum_congr rfl ?_
          intro g _hg
          by_cases hg : g.isSome = b
          · simp [hg]
          · simp [hg]
