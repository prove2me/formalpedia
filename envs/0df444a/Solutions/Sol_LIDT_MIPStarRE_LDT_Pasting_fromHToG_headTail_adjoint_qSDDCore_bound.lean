-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Pasting.fromHToG_headTail_adjoint_qSDDCore_bound
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T16:17:05.466929+00:00
-- url     : https://prove2.me/submissions/3af945c1-1eb2-4a77-a034-1eb2d5115729

-- Generated proof for MIPStarRE.LDT.Pasting.fromHToG_headTail_adjoint_qSDDCore_bound.
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
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_fromHToG_gHatHalfProduct_reverse_eq_adjoint
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_fromHToG_headTail_qSDDCore_bound
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_fromHToG_qSDDCore_symm

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
# Section 12 pasting: from-H-to-G collapsed bounds

Collapses the paper endpoint `M₄` to the next Lean stage and records the scalar
bounds used by the final telescope.
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
    (gamma zeta : _root_.LIDT.MIPStarRE.LDT.Error)
    (hgamma_nonneg : 0 ≤ gamma) (hzeta_nonneg : 0 ≤ zeta)
    (hhalf : ∀ j : ℕ, 2 ≤ j →
      _root_.LIDT.MIPStarRE.LDT.Pasting.CommuteGHalfSandwichStatement params ψbi family gamma zeta j)
    {n k : ℕ} (hn : 2 ≤ n + 1) (hnk : n + 1 ≤ k) :
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
  let eQ : (_root_.LIDT.MIPStarRE.LDT.Fq params × _root_.LIDT.MIPStarRE.LDT.PointTuple params n) ≃ (_root_.LIDT.MIPStarRE.LDT.Fq params × _root_.LIDT.MIPStarRE.LDT.PointTuple params n) :=
    (Function.Involutive.prodMap (f := id)
      (g := _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGPointTupleReverseEquiv params n) (fun _ => rfl)
      (_root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGPointTupleReverseEquiv params n).left_inv).toPerm
  let eO : (_root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n) ≃
      (_root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n) :=
    (Function.Involutive.prodMap (f := id)
      (g := _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGGHatTupleOutcomeReverseEquiv params n) (fun _ => rfl)
      (_root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGGHatTupleOutcomeReverseEquiv params n).left_inv).toPerm
  let baseIntegrand := fun q : _root_.LIDT.MIPStarRE.LDT.Fq params × _root_.LIDT.MIPStarRE.LDT.PointTuple params n =>
    _root_.LIDT.MIPStarRE.LDT.qSDDCore ψbi
      (fun ogs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n =>
        _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
          ((_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome ogs.1 *
            _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n q.2 ogs.2))
      (fun ogs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n =>
        _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
          (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n q.2 ogs.2 *
            (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome ogs.1))
  have hbase := _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToG_headTail_qSDDCore_bound params ψbi family gamma zeta
    hgamma_nonneg hzeta_nonneg hhalf (n := n) (k := k) hn hnk
  have hbase_reindexed :
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params × _root_.LIDT.MIPStarRE.LDT.PointTuple params n)) (fun q =>
        _root_.LIDT.MIPStarRE.LDT.qSDDCore ψbi
          (fun ogs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n =>
            _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
              ((_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome ogs.1 *
                _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n
                  ((_root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGPointTupleReverseEquiv params n) q.2) ogs.2))
          (fun ogs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n =>
            _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
              (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n
                  ((_root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGPointTupleReverseEquiv params n) q.2) ogs.2 *
                (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome ogs.1))) ≤
        _root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwichError params gamma zeta k := by
    calc
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params × _root_.LIDT.MIPStarRE.LDT.PointTuple params n)) (fun q =>
        _root_.LIDT.MIPStarRE.LDT.qSDDCore ψbi
          (fun ogs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n =>
            _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
              ((_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome ogs.1 *
                _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n
                  ((_root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGPointTupleReverseEquiv params n) q.2) ogs.2))
          (fun ogs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n =>
            _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
              (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n
                  ((_root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGPointTupleReverseEquiv params n) q.2) ogs.2 *
                (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome ogs.1)))
        = _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params × _root_.LIDT.MIPStarRE.LDT.PointTuple params n)) baseIntegrand := by
            simpa [baseIntegrand, eQ] using
              (_root_.LIDT.MIPStarRE.LDT.avgOver_uniform_equiv eQ baseIntegrand).symm
      _ ≤ _root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwichError params gamma zeta k := hbase
  have hsymm :
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params × _root_.LIDT.MIPStarRE.LDT.PointTuple params n)) (fun q =>
        _root_.LIDT.MIPStarRE.LDT.qSDDCore ψbi
          (fun ogs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n =>
            _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
              ((_root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n q.2 ogs.2)ᴴ *
                (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome ogs.1))
          (fun ogs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n =>
            _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
              ((_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome ogs.1 *
                (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n q.2 ogs.2)ᴴ))) =
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params × _root_.LIDT.MIPStarRE.LDT.PointTuple params n)) (fun q =>
        _root_.LIDT.MIPStarRE.LDT.qSDDCore ψbi
          (fun ogs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n =>
            _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
              ((_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome ogs.1 *
                (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n q.2 ogs.2)ᴴ))
          (fun ogs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n =>
            _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
              ((_root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n q.2 ogs.2)ᴴ *
                (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome ogs.1))) := by
    refine _root_.LIDT.MIPStarRE.LDT.avgOver_congr _ _ _ ?_
    intro q
    exact _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToG_qSDDCore_symm ψbi _ _
  have hrev :
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params × _root_.LIDT.MIPStarRE.LDT.PointTuple params n)) (fun q =>
        _root_.LIDT.MIPStarRE.LDT.qSDDCore ψbi
          (fun ogs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n =>
            _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
              ((_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome ogs.1 *
                (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n q.2 ogs.2)ᴴ))
          (fun ogs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n =>
            _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
              ((_root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n q.2 ogs.2)ᴴ *
                (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome ogs.1))) =
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params × _root_.LIDT.MIPStarRE.LDT.PointTuple params n)) (fun q =>
        _root_.LIDT.MIPStarRE.LDT.qSDDCore ψbi
          (fun ogs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n =>
            _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
              ((_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome ogs.1 *
                _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n
                  ((_root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGPointTupleReverseEquiv params n) q.2) ogs.2))
          (fun ogs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n =>
            _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
              (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n
                  ((_root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGPointTupleReverseEquiv params n) q.2) ogs.2 *
                (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome ogs.1))) := by
    refine _root_.LIDT.MIPStarRE.LDT.avgOver_congr _ _ _ ?_
    intro q
    unfold _root_.LIDT.MIPStarRE.LDT.qSDDCore
    exact Fintype.sum_equiv eO.symm
      (fun ogs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n =>
        let U := (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome ogs.1
        let T := _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n q.2 ogs.2
        _root_.LIDT.MIPStarRE.LDT.ev ψbi (((_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (U * Tᴴ) - _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (Tᴴ * U))ᴴ) *
          (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (U * Tᴴ) - _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (Tᴴ * U))))
      (fun ogs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n =>
        let U := (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome ogs.1
        let T := _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n
          ((_root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGPointTupleReverseEquiv params n) q.2) ogs.2
        _root_.LIDT.MIPStarRE.LDT.ev ψbi (((_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (U * T) - _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (T * U))ᴴ) *
          (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (U * T) - _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (T * U))))
      (by
        rintro ⟨g, gs⟩
        let U := (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome g
        have hT :
            _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n
                ((_root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGPointTupleReverseEquiv params n) q.2)
                ((_root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGGHatTupleOutcomeReverseEquiv params n) gs) =
              (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n q.2 gs)ᴴ := by
          simpa using _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToG_gHatHalfProduct_reverse_eq_adjoint params family n q.2 gs
        let F := fun T : _root_.LIDT.MIPStarRE.Quantum.Op ι =>
          _root_.LIDT.MIPStarRE.LDT.ev ψbi (((_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (U * T) - _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (T * U))ᴴ) *
            (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (U * T) - _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (T * U)))
        simpa [F, U, eO] using congrArg F hT.symm)
  calc
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params × _root_.LIDT.MIPStarRE.LDT.PointTuple params n)) (fun q =>
      _root_.LIDT.MIPStarRE.LDT.qSDDCore ψbi
        (fun ogs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n =>
          _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
            ((_root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n q.2 ogs.2)ᴴ *
              (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome ogs.1))
        (fun ogs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n =>
          _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
            ((_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome ogs.1 *
              (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n q.2 ogs.2)ᴴ)))
      = _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params × _root_.LIDT.MIPStarRE.LDT.PointTuple params n)) (fun q =>
          _root_.LIDT.MIPStarRE.LDT.qSDDCore ψbi
            (fun ogs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n =>
              _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                ((_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome ogs.1 *
                  (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n q.2 ogs.2)ᴴ))
            (fun ogs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n =>
              _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                ((_root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n q.2 ogs.2)ᴴ *
                  (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome ogs.1))) := hsymm
    _ = _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params × _root_.LIDT.MIPStarRE.LDT.PointTuple params n)) (fun q =>
          _root_.LIDT.MIPStarRE.LDT.qSDDCore ψbi
            (fun ogs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n =>
              _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                ((_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome ogs.1 *
                  _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n
                    ((_root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGPointTupleReverseEquiv params n) q.2) ogs.2))
            (fun ogs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n =>
              _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n
                    ((_root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGPointTupleReverseEquiv params n) q.2) ogs.2 *
                  (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome ogs.1))) := hrev
    _ ≤ _root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwichError params gamma zeta k := hbase_reindexed
