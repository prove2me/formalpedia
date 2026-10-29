-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Pasting.fromHToG_ev_sum_isSome_sandwich_weight
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T15:47:37.550081+00:00
-- url     : https://prove2.me/submissions/a0b89a3f-a9b4-4ab2-8541-5d6f80a0f8f0

-- Generated proof for MIPStarRE.LDT.Pasting.fromHToG_ev_sum_isSome_sandwich_weight.
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
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_fromHToG_gHatIdxMeas_sum_isSome_false
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_fromHToG_gHatIdxMeas_sum_isSome_true

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
# Section 12 pasting: from-H-to-G S U S context-average bounds

Sandwich-sum identities and the `S U S` context-average bound used in the
second half-sandwich and final move-right Cauchy--Schwarz steps.
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
    (family : _root_.LIDT.MIPStarRE.LDT.IdxPolyFamily params ι) (x : _root_.LIDT.MIPStarRE.LDT.Fq params)
    (b : Bool) (A S : _root_.LIDT.MIPStarRE.Quantum.Op ι) :
    (∑ g ∈ (Finset.univ : Finset (_root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params)) with g.isSome = b,
        _root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) A *
          _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι)
            (S * (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family x).outcome g * S))) =
      _root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) A *
        _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι)
          (S * (if b then (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family x).total
            else (_root_.LIDT.MIPStarRE.LDT.Pasting.incompletePartSubMeas params family x).total) * S)) := by
  classical
  rw [← _root_.LIDT.MIPStarRE.LDT.ev_finset_sum]
  congr 1
  cases b
  · calc
      (∑ g ∈ (Finset.univ : Finset (_root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params)) with g.isSome = false,
          _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) A *
            _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι)
              (S * (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family x).outcome g * S))
        = _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) A *
            (∑ g ∈ (Finset.univ : Finset (_root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params)) with g.isSome = false,
              _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι)
                (S * (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family x).outcome g * S)) := by
            rw [Finset.mul_sum]
      _ = _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) A *
            _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι)
              (∑ g ∈ (Finset.univ : Finset (_root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params)) with g.isSome = false,
                S * (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family x).outcome g * S) := by
            rw [_root_.LIDT.MIPStarRE.LDT.rightTensor_finset_sum]
      _ = _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) A *
            _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι)
              ((∑ g ∈ (Finset.univ : Finset (_root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params)) with g.isSome = false,
                  S * (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family x).outcome g) * S) := by
            rw [Finset.sum_mul]
      _ = _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) A *
            _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι)
              (S * (∑ g ∈ (Finset.univ : Finset (_root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params)) with g.isSome = false,
                  (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family x).outcome g) * S) := by
            rw [Finset.mul_sum]
      _ = _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) A *
            _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι)
              (S * (_root_.LIDT.MIPStarRE.LDT.Pasting.incompletePartSubMeas params family x).total * S) := by
            rw [_root_.LIDT.MIPStarRE.LDT.Pasting.fromHToG_gHatIdxMeas_sum_isSome_false]
      _ = _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) A *
            _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι)
              (S * (if false then (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family x).total
                else (_root_.LIDT.MIPStarRE.LDT.Pasting.incompletePartSubMeas params family x).total) * S) := by simp
  · calc
      (∑ g ∈ (Finset.univ : Finset (_root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params)) with g.isSome = true,
          _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) A *
            _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι)
              (S * (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family x).outcome g * S))
        = _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) A *
            (∑ g ∈ (Finset.univ : Finset (_root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params)) with g.isSome = true,
              _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι)
                (S * (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family x).outcome g * S)) := by
            rw [Finset.mul_sum]
      _ = _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) A *
            _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι)
              (∑ g ∈ (Finset.univ : Finset (_root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params)) with g.isSome = true,
                S * (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family x).outcome g * S) := by
            rw [_root_.LIDT.MIPStarRE.LDT.rightTensor_finset_sum]
      _ = _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) A *
            _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι)
              ((∑ g ∈ (Finset.univ : Finset (_root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params)) with g.isSome = true,
                  S * (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family x).outcome g) * S) := by
            rw [Finset.sum_mul]
      _ = _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) A *
            _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι)
              (S * (∑ g ∈ (Finset.univ : Finset (_root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params)) with g.isSome = true,
                  (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family x).outcome g) * S) := by
            rw [Finset.mul_sum]
      _ = _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) A *
            _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι)
              (S * (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family x).total * S) := by
            rw [_root_.LIDT.MIPStarRE.LDT.Pasting.fromHToG_gHatIdxMeas_sum_isSome_true]
      _ = _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) A *
            _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι)
              (S * (if true then (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family x).total
                else (_root_.LIDT.MIPStarRE.LDT.Pasting.incompletePartSubMeas params family x).total) * S) := by simp
