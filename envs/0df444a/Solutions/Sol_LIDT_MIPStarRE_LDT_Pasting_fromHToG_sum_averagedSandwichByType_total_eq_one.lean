-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Pasting.fromHToG_sum_averagedSandwichByType_total_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T15:58:31.437819+00:00
-- url     : https://prove2.me/submissions/61accc55-9d05-40d4-9b65-c98c394ec538

-- Generated proof for MIPStarRE.LDT.Pasting.fromHToG_sum_averagedSandwichByType_total_eq_one.
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
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_fromHToG_type_filtered_outcome_sum
import Theorems.Thm_LIDT_MIPStarRE_LDT_averageOperatorOverDistribution_const_of_isProbability

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

/- Source helpers from MIPStarRE/LDT/Pasting/Bernoulli/FromHToG/Core/AveragesAndOps.lean. -/
/-!
# Section 12 pasting: operator averages and projective submeasurement lemmas

Averages over uniform distributions, tensor placement identities, and
projective submeasurement algebraic lemmas for the `fromHToG` reduction.
-/

@[expose] public section

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma fromHToG_averageOperator_uniform_const_one
    (α : Type*) [Fintype α] [DecidableEq α] [Nonempty α] :
    averageOperatorOverDistribution (uniformDistribution α)
      (fun _ : α => (1 : MIPStarRE.Quantum.Op ι)) = 1 := by
  exact averageOperatorOverDistribution_const_of_isProbability
    (uniformDistribution α) (uniformDistribution_isProbability α) 1



























end MIPStarRE.LDT.Pasting

end

/- Source helpers from MIPStarRE/LDT/Pasting/Bernoulli/FromHToG/Core/StageMass.lean. -/
/-!
# Section 12 pasting: from-H-to-G stage-mass bookkeeping

Stage-`0` identification, terminal identification, adjacent-stage split, and
telescoping lemmas that connect the Lean recurrence stages to the paper scalars.
-/

@[expose] public section

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]





/-- Membership in `outcomesByType τ` is the same as having tuple type `τ`. -/
lemma fromHToG_outcomesByType_iff_type_eq
    {params : Parameters} [FieldModel params.q] {k : ℕ}
    (gs : GHatTupleOutcome params k) (τ : GHatType k) :
    gs ∈ outcomesByType τ ↔ gHatTupleType gs = τ := by
  simp [outcomesByType, gHatTupleType, funext_iff]





/-- The per-type averaged sandwich total is the uniform average of the exact-type
fibers of `gHatSandwichFamily`. -/
lemma fromHToG_averagedSandwichByType_total_eq_type_sum
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ) (τ : GHatType k) :
    (averagedSandwichByTypeSubMeas params family k τ).total =
      ∑ xs ∈ (uniformDistribution (PointTuple params k)).support,
        (uniformDistribution (PointTuple params k)).weight xs •
          (∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params k)) with
            gHatTupleType gs = τ,
            (gHatSandwichFamily params family k xs).outcome gs) := by
  classical
  simp only [averagedSandwichByTypeSubMeas, averageIdxSubMeas,
    averageOperatorOverDistribution]
  refine Finset.sum_congr rfl ?_
  intro xs _hxs
  congr 1
  simp [restrictSubMeas, postprocess, fromHToG_outcomesByType_iff_type_eq]

-- This declaration expands a finite operator average into the corresponding
-- scalar trace average; the displayed statement is less readable after writing
-- the fully expanded finite-sum target as an intermediate `suffices`.


-- This declaration is the right-register analogue of the preceding finite-sum
-- expansion; spelling out the simplified scalar target obscures the average
-- identity being proved.
















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
    (family : _root_.LIDT.MIPStarRE.LDT.IdxPolyFamily params ι) (n : ℕ) :
    (∑ τ : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatType n,
      (_root_.LIDT.MIPStarRE.LDT.Pasting.averagedSandwichByTypeSubMeas params family n τ).total) = 1 := by
  classical
  calc
    (∑ τ : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatType n, (_root_.LIDT.MIPStarRE.LDT.Pasting.averagedSandwichByTypeSubMeas params family n τ).total)
      = ∑ τ : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatType n,
          ∑ xs ∈ (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.PointTuple params n)).support,
            (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.PointTuple params n)).weight xs •
              (∑ gs ∈ (Finset.univ : Finset (_root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n)) with
                _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleType gs = τ,
                (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatSandwichFamily params family n xs).outcome gs) := by
            refine Finset.sum_congr rfl ?_
            intro τ _hτ
            rw [_root_.LIDT.MIPStarRE.LDT.Pasting.fromHToG_averagedSandwichByType_total_eq_type_sum params family n τ]
    _ = ∑ xs ∈ (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.PointTuple params n)).support,
          ∑ τ : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatType n,
            (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.PointTuple params n)).weight xs •
              (∑ gs ∈ (Finset.univ : Finset (_root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n)) with
                _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleType gs = τ,
                (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatSandwichFamily params family n xs).outcome gs) := by
            rw [Finset.sum_comm]
    _ = ∑ xs ∈ (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.PointTuple params n)).support,
          (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.PointTuple params n)).weight xs •
            (∑ τ : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatType n,
              ∑ gs ∈ (Finset.univ : Finset (_root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n)) with
                _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleType gs = τ,
                (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatSandwichFamily params family n xs).outcome gs) := by
            refine Finset.sum_congr rfl ?_
            intro xs _hxs
            rw [Finset.smul_sum]
    _ = ∑ xs ∈ (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.PointTuple params n)).support,
          (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.PointTuple params n)).weight xs •
            (∑ gs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n,
              (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatSandwichFamily params family n xs).outcome gs) := by
            refine Finset.sum_congr rfl ?_
            intro xs _hxs
            exact congrArg
              ((_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.PointTuple params n)).weight xs • ·)
              (_root_.LIDT.MIPStarRE.LDT.Pasting.fromHToG_type_filtered_outcome_sum params
                (fun τ gs => (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatSandwichFamily params family n xs).outcome gs))
    _ = ∑ xs ∈ (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.PointTuple params n)).support,
          (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.PointTuple params n)).weight xs •
            (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) := by
            refine Finset.sum_congr rfl ?_
            intro xs _hxs
            rw [_root_.LIDT.MIPStarRE.LDT.Pasting.fromHToG_gHatSandwichFamily_sum_eq_one params family n xs]
    _ = 1 := by
          simpa [_root_.LIDT.MIPStarRE.LDT.averageOperatorOverDistribution] using
            (_root_.LIDT.MIPStarRE.LDT.Pasting.fromHToG_averageOperator_uniform_const_one (ι := ι) (α := _root_.LIDT.MIPStarRE.LDT.PointTuple params n))
