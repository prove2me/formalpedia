-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Pasting.fromHToG_averagedEligibleSandwich_total_eq_type_sum
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T15:38:53.089255+00:00
-- url     : https://prove2.me/submissions/65b0e028-7235-4f5e-b284-788d5a7e86ec

-- Generated proof for MIPStarRE.LDT.Pasting.fromHToG_averagedEligibleSandwich_total_eq_type_sum.
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
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_fromHToG_interpolationEligibleSandwich_total_eq_type_sum

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

end LIDT

open LIDT
/-!
# Section 12 pasting: from-H-to-G stage-mass bookkeeping

Stage-`0` identification, terminal identification, adjacent-stage split, and
telescoping lemmas that connect the Lean recurrence stages to the paper scalars.
-/

@[expose] public section

open LIDT.MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]













-- This declaration expands a finite operator average into the corresponding
-- scalar trace average; the displayed statement is less readable after writing
-- the fully expanded finite-sum target as an intermediate `suffices`.


-- This declaration is the right-register analogue of the preceding finite-sum
-- expansion; spelling out the simplified scalar target obscures the average
-- identity being proved.

theorem solution
    (params : _root_.LIDT.MIPStarRE.LDT.Parameters) [_root_.LIDT.MIPStarRE.LDT.FieldModel params.q]
    (family : _root_.LIDT.MIPStarRE.LDT.IdxPolyFamily params ι) (k : ℕ) :
    (_root_.LIDT.MIPStarRE.LDT.Pasting.averagedEligibleSandwichSubMeas params family k).total =
      ∑ τ : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatType k,
        if params.d + 1 ≤ _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeWeight τ then
          (_root_.LIDT.MIPStarRE.LDT.Pasting.averagedSandwichByTypeSubMeas params family k τ).total
        else 0 := by
  classical
  simp only [_root_.LIDT.MIPStarRE.LDT.Pasting.averagedEligibleSandwichSubMeas, _root_.LIDT.MIPStarRE.LDT.averageIdxSubMeas,
    _root_.LIDT.MIPStarRE.LDT.averageOperatorOverDistribution]
  calc
    (∑ a ∈ (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.PointTuple params k)).support,
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.PointTuple params k)).weight a •
          (_root_.LIDT.MIPStarRE.LDT.Pasting.interpolationEligibleSandwichFamily params family k a).total)
      = ∑ a ∈ (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.PointTuple params k)).support,
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.PointTuple params k)).weight a •
          (∑ τ : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatType k,
            if params.d + 1 ≤ _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeWeight τ then
              ∑ gs ∈ (Finset.univ : Finset (_root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params k)) with
                _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleType gs = τ,
                (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatSandwichFamily params family k a).outcome gs
            else 0) := by
          refine Finset.sum_congr rfl ?_
          intro a _ha
          rw [_root_.LIDT.MIPStarRE.LDT.Pasting.fromHToG_interpolationEligibleSandwich_total_eq_type_sum]
    _ = ∑ a ∈ (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.PointTuple params k)).support,
          ∑ τ : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatType k,
            (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.PointTuple params k)).weight a •
              (if params.d + 1 ≤ _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeWeight τ then
                ∑ gs ∈ (Finset.univ : Finset (_root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params k)) with
                  _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleType gs = τ,
                  (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatSandwichFamily params family k a).outcome gs
              else 0) := by
          refine Finset.sum_congr rfl ?_
          intro a _ha
          rw [Finset.smul_sum]
    _ = ∑ τ : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatType k,
        ∑ a ∈ (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.PointTuple params k)).support,
            (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.PointTuple params k)).weight a •
              (if params.d + 1 ≤ _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeWeight τ then
                ∑ gs ∈ (Finset.univ : Finset (_root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params k)) with
                  _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleType gs = τ,
                  (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatSandwichFamily params family k a).outcome gs
              else 0) := by
          rw [Finset.sum_comm]
    _ = ∑ τ : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatType k,
        if params.d + 1 ≤ _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeWeight τ then
          ∑ a ∈ (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.PointTuple params k)).support,
            (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.PointTuple params k)).weight a •
              (∑ gs ∈ (Finset.univ : Finset (_root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params k)) with
                _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleType gs = τ,
                (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatSandwichFamily params family k a).outcome gs)
        else 0 := by
          refine Finset.sum_congr rfl ?_
          intro τ _hτmem
          by_cases hτ : params.d + 1 ≤ _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeWeight τ <;> simp [hτ]
    _ = ∑ τ : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatType k,
        if params.d + 1 ≤ _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeWeight τ then
          (_root_.LIDT.MIPStarRE.LDT.Pasting.averagedSandwichByTypeSubMeas params family k τ).total
        else 0 := by
          refine Finset.sum_congr rfl ?_
          intro τ _hτ
          by_cases hτelig : params.d + 1 ≤ _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeWeight τ <;>
            simp [hτelig, _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToG_averagedSandwichByType_total_eq_type_sum]
