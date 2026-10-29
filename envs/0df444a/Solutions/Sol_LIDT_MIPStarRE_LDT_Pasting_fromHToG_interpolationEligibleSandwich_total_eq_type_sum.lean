-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Pasting.fromHToG_interpolationEligibleSandwich_total_eq_type_sum
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T15:34:17.947444+00:00
-- url     : https://prove2.me/submissions/5eb71b6c-2780-434d-afe0-594983e249c5

-- Generated proof for MIPStarRE.LDT.Pasting.fromHToG_interpolationEligibleSandwich_total_eq_type_sum.
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







/-- Interpolation eligibility depends only on the Boolean type of a completed-slice
tuple. -/
lemma fromHToG_interpolationEligible_iff_type_weight
    (params : Parameters) [FieldModel params.q] {k : ℕ}
    (gs : GHatTupleOutcome params k) :
    InterpolationEligible params gs ↔
      params.d + 1 ≤ gHatTypeWeight (gHatTupleType gs) := by
  simp [InterpolationEligible, gHatTupleHammingWeight, gHatTupleSupport,
    gHatTypeWeight, gHatTupleType]
  rfl





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

theorem solution
    (params : _root_.LIDT.MIPStarRE.LDT.Parameters) [_root_.LIDT.MIPStarRE.LDT.FieldModel params.q]
    (family : _root_.LIDT.MIPStarRE.LDT.IdxPolyFamily params ι) (k : ℕ) (xs : _root_.LIDT.MIPStarRE.LDT.PointTuple params k) :
    (_root_.LIDT.MIPStarRE.LDT.Pasting.interpolationEligibleSandwichFamily params family k xs).total =
      ∑ τ : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatType k,
        if params.d + 1 ≤ _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeWeight τ then
          ∑ gs ∈ (Finset.univ : Finset (_root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params k)) with
            _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleType gs = τ,
            (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatSandwichFamily params family k xs).outcome gs
        else 0 := by
  classical
  let A : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params k → _root_.LIDT.MIPStarRE.Quantum.Op ι :=
    fun gs => (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatSandwichFamily params family k xs).outcome gs
  have hpartition :
      (∑ gs ∈ (Finset.univ : Finset (_root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params k)) with
          _root_.LIDT.MIPStarRE.LDT.Pasting.InterpolationEligible params gs, A gs) =
        ∑ τ : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatType k,
          if params.d + 1 ≤ _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeWeight τ then
            ∑ gs ∈ (Finset.univ : Finset (_root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params k)) with
              _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleType gs = τ, A gs
          else 0 := by
    calc
      (∑ gs ∈ (Finset.univ : Finset (_root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params k)) with
          _root_.LIDT.MIPStarRE.LDT.Pasting.InterpolationEligible params gs, A gs)
        = ∑ gs ∈ (Finset.univ : Finset (_root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params k)),
            if _root_.LIDT.MIPStarRE.LDT.Pasting.InterpolationEligible params gs then A gs else 0 := by
            rw [Finset.sum_filter]
      _ = ∑ τ : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatType k,
            ∑ gs ∈ (Finset.univ : Finset (_root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params k)) with
              _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleType gs = τ,
              if _root_.LIDT.MIPStarRE.LDT.Pasting.InterpolationEligible params gs then A gs else 0 := by
            exact (Finset.sum_fiberwise
              (Finset.univ : Finset (_root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params k))
              (fun gs => _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleType gs)
              (fun gs => if _root_.LIDT.MIPStarRE.LDT.Pasting.InterpolationEligible params gs then A gs else 0)).symm
      _ = ∑ τ : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatType k,
          if params.d + 1 ≤ _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeWeight τ then
            ∑ gs ∈ (Finset.univ : Finset (_root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params k)) with
              _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleType gs = τ, A gs
          else 0 := by
          refine Finset.sum_congr rfl ?_
          intro τ _
          by_cases hτ : params.d + 1 ≤ _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeWeight τ
          · rw [if_pos hτ]
            refine Finset.sum_congr rfl ?_
            intro gs hgs
            simp only [Finset.mem_filter] at hgs
            have htype : _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleType gs = τ := hgs.2
            have helig : _root_.LIDT.MIPStarRE.LDT.Pasting.InterpolationEligible params gs := by
              rw [_root_.LIDT.MIPStarRE.LDT.Pasting.fromHToG_interpolationEligible_iff_type_weight params gs]
              simpa [htype] using hτ
            rw [if_pos helig]
          · rw [if_neg hτ]
            refine Finset.sum_eq_zero ?_
            intro gs hgs
            simp only [Finset.mem_filter] at hgs
            have htype : _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleType gs = τ := hgs.2
            have hnot : ¬ _root_.LIDT.MIPStarRE.LDT.Pasting.InterpolationEligible params gs := by
              intro helig
              have hw := (_root_.LIDT.MIPStarRE.LDT.Pasting.fromHToG_interpolationEligible_iff_type_weight params gs).1 helig
              exact hτ (by simpa [htype] using hw)
            rw [if_neg hnot]
  simpa [_root_.LIDT.MIPStarRE.LDT.Pasting.interpolationEligibleSandwichFamily, _root_.LIDT.MIPStarRE.LDT.Pasting.restrictSubMeas, A] using hpartition
