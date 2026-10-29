-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Pasting.overAllOutcomes_ofLinePointBounds
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T16:55:34.697746+00:00
-- url     : https://prove2.me/submissions/325464a4-fb8a-48b6-8742-c548450137ec

-- Generated proof for MIPStarRE.LDT.Pasting.overAllOutcomes_ofLinePointBounds.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_MoveChain_BackChain
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_MoveChain_Base
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_MoveChain_Chain
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_MoveChain_FlatChain
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_MoveChain_Lifting
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_Setup_Definitions
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LdSandwichLineOnePoint_CSSetup
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LdSandwichLineOnePoint_Endpoint
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LdSandwichLineOnePoint_EndpointEquivs
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LdSandwichLineOnePoint_PrefixMoved
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LineInterpolation_BadLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LineInterpolation_BadMass
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LineInterpolation_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_OverAllOutcomes_NonglobalDecomposition
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Core_LdGbcon
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Triangles_Core
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
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_avgOver_distinct_badMass_le_hBConsistencyError_ofLinePointBounds
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_avgOver_distinct_eligibleMass_eq_global_add_nonglobal
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_avgOver_uniform_eligibleMass_le_distinct_add_dnoteq
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_dnoteq_term_le_overAllOutcomesError
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_hBConsistencyError_add_mdq_add_dnoteq_le_overAllOutcomesError
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_overAllOutcomes_distinct_nonglobal_mass_le_bad_line_mass_add_lineConsistent
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_overAllOutcomes_pasted_sub_expansion_le_dnoteq
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_overAllOutcomes_reverse_mass_bound_of_not_d_add_one_le
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_restrictToVerticalLine_eval_eq_restrictAtHeight_eval
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_tupleInterpolatedVerticalLine_eq_of_no_supported_mismatch

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

/- Source helpers from MIPStarRE/LDT/Pasting/ComparisonLemmas/LineInterpolation/Core.lean. -/
/-!
# Line interpolation: core API

Interpolation-support, vertical-line restriction, and completed-slice
interpolation lemmas from `ld-pasting.tex` that form the foundation for the
line-interpolation estimates.

## References

- `references/ldt-paper/ld-pasting.tex`
- `blueprint/src/chapter/ch09_pasting.tex`
-/

@[expose] public section

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]



lemma nonglobal_gives_slice_mismatch_against_interpolant
    (params : Parameters) [FieldModel params.q]
    {k : ℕ}
    (xs : PointTuple params k)
    (gs : GHatTupleOutcome params k)
    (hNGlobal : ¬ IsGloballyConsistent params xs gs) :
    ∃ i : Fin k, ∃ hiSome : (gs i).isSome = true,
      Polynomial.restrictAtHeight params
        (interpolateCompletedSlices params k xs gs) (xs i) ≠
      (gs i).get hiSome := by
  classical
  let hStar := interpolateCompletedSlices params k xs gs
  by_contra hcontra
  push Not at hcontra
  apply hNGlobal
  refine ⟨hStar, ?_⟩
  intro i hiSome
  exact congrArg Polynomial.poly (hcontra i hiSome)















end MIPStarRE.LDT.Pasting

end

/- Source helpers from MIPStarRE/LDT/Pasting/ComparisonLemmas/OverAllOutcomes/ErrorAndMass.lean. -/
/-!
# Section 12 pasting: over all outcomes — error terms and eligible mass

Error-arithmetic lemmas, eligible-mass bounds, and mass identities that feed the final
`lem:over-all-outcomes` comparison.

## References

- `references/ldt-paper/ld-pasting.tex`
- `blueprint/src/chapter/ch09_pasting.tex`
-/

@[expose] public section

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]







/-- Eligible interpolation mass is at most one for every point tuple. -/
lemma eligibleMass_le_one
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) {k : ℕ} (xs : PointTuple params k) :
    subMeasMass strategy.state
      ((interpolationEligibleSandwichFamily params family k xs).liftLeft) ≤ 1 := by
  unfold subMeasMass SubMeas.liftLeft
  have hle :
      leftTensor (ι₂ := ι)
        (interpolationEligibleSandwichFamily params family k xs).total ≤
        (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
    exact leftTensor_le_one (ι₂ := ι)
      (interpolationEligibleSandwichFamily params family k xs).total_le_one
  simpa [ev_one_of_isNormalized strategy.state strategy.isNormalized] using
    ev_mono strategy.state _ _ hle





/-- The pasted mass is the distinct average of globally consistent eligible mass. -/
lemma overAllOutcomesPastedMass_eq_avg_distinct_global
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) (k : ℕ) :
    overAllOutcomesPastedMass params strategy family k =
      avgOver (distinctTupleDistribution params k) (fun xs =>
        subMeasMass strategy.state
          ((restrictSubMeas (interpolationEligibleSandwichFamily params family k xs)
            (IsGloballyConsistent params xs)).liftLeft)) := by
  simp only [overAllOutcomesPastedMass, constructedPastedSubMeas, pastedInterpolationFamily,
    subMeasMass, SubMeas.liftLeft, averageIdxSubMeas, postprocess_total]
  exact ev_leftTensor_averageOperatorOverDistribution strategy.state
    (distinctTupleDistribution params k)
    (fun xs =>
      (restrictSubMeas (interpolationEligibleSandwichFamily params family k xs)
        (IsGloballyConsistent params xs)).total)

/-- The expansion mass is the uniform average of eligible interpolation mass. -/
lemma overAllOutcomesExpansionMass_eq_avg_uniform_eligible
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) (k : ℕ) :
    overAllOutcomesExpansionMass params strategy family k =
      avgOver (uniformDistribution (PointTuple params k)) (fun xs =>
        subMeasMass strategy.state
          ((interpolationEligibleSandwichFamily params family k xs).liftLeft)) := by
  simp only [overAllOutcomesExpansionMass, allOutcomesExpansionFamily,
    averagedEligibleSandwichSubMeas, pastedMeasurementTotal, constSubMeasFamily,
    subMeasMass, SubMeas.liftLeft, IdxSubMeas.liftLeft, averageIdxSubMeas]
  exact ev_leftTensor_averageOperatorOverDistribution strategy.state
    (uniformDistribution (PointTuple params k))
    (fun xs => (interpolationEligibleSandwichFamily params family k xs).total)











end MIPStarRE.LDT.Pasting

end

/- Source helpers from MIPStarRE/LDT/Pasting/ComparisonLemmas/OverAllOutcomes/NonglobalDecomposition.lean. -/
/-!
# Section 12 pasting: over all outcomes — nonglobal-mass decomposition

Nonglobal-mass definitions, the vertical-line insertion, and the line-consistency
decomposition that splits the nonglobal eligible mass into the bad-line event and
the line-consistent residual.

## References

- `references/ldt-paper/ld-pasting.tex`
- `blueprint/src/chapter/ch09_pasting.tex`
-/

@[expose] public section

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]









/-- The one-point line comparison hypotheses bound the inserted line-mismatch
mass by the displayed `hBConsistency` error.

Paper route: this is the aggregation in `ld-pasting.tex` lines 1186--1202,
using `prop:ld-dnoteq` plus `lem:ld-sandwich-line-one-point`. -/
lemma overAllOutcomes_distinct_bad_line_mass_le_hBConsistencyError
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (eps delta gamma zeta : Error) (k : ℕ)
    (hd : 0 < params.d)
    (heps_nonneg : 0 ≤ eps)
    (hdelta_nonneg : 0 ≤ delta)
    (hgamma_nonneg : 0 ≤ gamma)
    (hzeta_nonneg : 0 ≤ zeta)
    (hline : ∀ i : ℕ, i < k →
      LdSandwichLineOnePointStatement params strategy family
        eps delta gamma zeta k i) :
    overAllOutcomesDistinctBadLineMass params strategy family k ≤
      hBConsistencyError params eps delta gamma zeta k := by
  simpa [overAllOutcomesDistinctBadLineMass] using
    avgOver_distinct_badMass_le_hBConsistencyError_ofLinePointBounds
      params strategy family eps delta gamma zeta k hd
      heps_nonneg hdelta_nonneg hgamma_nonneg hzeta_nonneg hline

/-- The vertical-line measurement is a genuine measurement, so its total is `1`.
This is the formal counterpart of the line `because B is a measurement` at
`ld-pasting.tex` lines 1178--1180. -/
private lemma verticalLineMeasurementFamily_total_eq_one
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (u : Point params) :
    (verticalLineMeasurementFamily params strategy u).total = 1 := by
  let ℓ : AxisParallelLine params.next :=
    { base := appendPoint params u zeroCoord
      direction := lastCoord params }
  simpa [verticalLineMeasurementFamily, ℓ] using
    (strategy.axisParallelMeasurement ℓ).total_eq_one















/-- The explicit line-answer version of the line-consistent residual is bounded by
its consistency-indicator version, after summing out the vertical-line
measurement. -/
private lemma lineConsistentLocal_le_indicatorLocal
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) {k : ℕ}
    (u : Point params) (xs : PointTuple params k) :
    overAllOutcomesLineConsistentNonglobalLocal params strategy family u xs ≤
      overAllOutcomesLineConsistentIndicatorLocal params strategy family u xs := by
  classical
  let A := interpolationEligibleSandwichFamily params family k xs
  let B := verticalLineMeasurementFamily params strategy u
  let T : MIPStarRE.Quantum.Op ι :=
    ∑ gs : GHatTupleOutcome params k,
      if (¬ IsGloballyConsistent params xs gs) ∧
          ∃ f : AxisLinePolynomial params.next,
            ¬ (∃ i : Fin k, ∃ hiSome : (gs i).isSome = true,
              ((gs i).get hiSome) u ≠ f (xs i)) then
        A.outcome gs
      else 0
  have hT :
      (restrictSubMeas A (fun gs => (¬ IsGloballyConsistent params xs gs) ∧
        ∃ f : AxisLinePolynomial params.next,
          ¬ (∃ i : Fin k, ∃ hiSome : (gs i).isSome = true,
            ((gs i).get hiSome) u ≠ f (xs i)))).total = T := by
    change (∑ gs ∈ (Finset.univ.filter
        (fun gs : GHatTupleOutcome params k =>
          (¬ IsGloballyConsistent params xs gs) ∧
            ∃ f : AxisLinePolynomial params.next,
              ¬ (∃ i : Fin k, ∃ hiSome : (gs i).isSome = true,
                ((gs i).get hiSome) u ≠ f (xs i)))), A.outcome gs) = T
    simp [T, Finset.sum_filter]
  have hBtotal : B.total = 1 := by
    simpa [B] using verticalLineMeasurementFamily_total_eq_one params strategy u
  have hterm : ∀ f : AxisLinePolynomial params.next,
      ev strategy.state
        (opTensor
          (∑ gs : GHatTupleOutcome params k,
            if (¬ IsGloballyConsistent params xs gs) ∧
                ¬ (∃ i : Fin k, ∃ hiSome : (gs i).isSome = true,
                  ((gs i).get hiSome) u ≠ f (xs i)) then
              A.outcome gs
            else 0)
          (B.outcome f)) ≤
        ev strategy.state (opTensor T (B.outcome f)) := by
    intro f
    apply ev_mono strategy.state _ _
    apply opTensor_mono_left
    · dsimp [T]
      refine Finset.sum_le_sum ?_
      intro gs _
      by_cases hlocal : (¬ IsGloballyConsistent params xs gs) ∧
          ¬ (∃ i : Fin k, ∃ hiSome : (gs i).isSome = true,
            ((gs i).get hiSome) u ≠ f (xs i))
      · have hind : (¬ IsGloballyConsistent params xs gs) ∧
            ∃ f : AxisLinePolynomial params.next,
              ¬ (∃ i : Fin k, ∃ hiSome : (gs i).isSome = true,
                ((gs i).get hiSome) u ≠ f (xs i)) :=
          ⟨hlocal.1, ⟨f, hlocal.2⟩⟩
        rw [if_pos hlocal, if_pos hind]
      · by_cases hind : (¬ IsGloballyConsistent params xs gs) ∧
            ∃ f : AxisLinePolynomial params.next,
              ¬ (∃ i : Fin k, ∃ hiSome : (gs i).isSome = true,
                ((gs i).get hiSome) u ≠ f (xs i))
        · rw [if_neg hlocal, if_pos hind]
          exact A.outcome_pos gs
        · rw [if_neg hlocal, if_neg hind]
    · exact B.outcome_pos f
  calc
    overAllOutcomesLineConsistentNonglobalLocal params strategy family u xs
      ≤ ∑ f : AxisLinePolynomial params.next,
          ev strategy.state (opTensor T (B.outcome f)) := by
          unfold overAllOutcomesLineConsistentNonglobalLocal
          dsimp [A, B]
          exact Finset.sum_le_sum fun f _ => hterm f
    _ = ev strategy.state (opTensor T (∑ f : AxisLinePolynomial params.next, B.outcome f)) := by
          rw [← ev_finset_sum, ← opTensor_sum_right_finset]
    _ = ev strategy.state (opTensor T B.total) := by rw [B.sum_eq_total]
    _ = ev strategy.state (opTensor T (1 : MIPStarRE.Quantum.Op ι)) := by rw [hBtotal]
    _ = overAllOutcomesLineConsistentIndicatorLocal params strategy family u xs := by
          unfold overAllOutcomesLineConsistentIndicatorLocal subMeasMass SubMeas.liftLeft
          rw [mkLeftPlacedSubMeas_total, hT]

/-- Averaged line-consistent residual after the explicit line answer is summed out. -/
lemma lineConsistentNonglobalMass_le_indicatorMass
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) (k : ℕ) :
    overAllOutcomesDistinctLineConsistentNonglobalMass params strategy family k ≤
      overAllOutcomesDistinctLineConsistentIndicatorMass params strategy family k := by
  unfold overAllOutcomesDistinctLineConsistentNonglobalMass
    overAllOutcomesDistinctLineConsistentIndicatorMass
  apply avgOver_mono
  intro u
  apply avgOver_mono
  intro xs
  exact lineConsistentLocal_le_indicatorLocal params strategy family u xs



end MIPStarRE.LDT.Pasting

end

/- Source helpers from MIPStarRE/LDT/Pasting/ComparisonLemmas/OverAllOutcomes/Final.lean. -/
/-!
# Section 12 pasting: over all outcomes — Schwartz–Zippel bounds and final assembly

Schwartz–Zippel aggregation, the line-consistent indicator bound, and the final chained
assembly of `lem:over-all-outcomes`.

## References

- `references/ldt-paper/ld-pasting.tex`
- `blueprint/src/chapter/ch09_pasting.tex`
-/

@[expose] public section

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- For a fixed distinct tuple and interpolation-eligible nonglobal outcome, the
probability (over the vertical-line base point `u`) of the line-consistency
indicator is bounded by the paper's `md/q` Schwartz--Zippel term.

This formalizes `ld-pasting.tex` lines 1256--1265: nonglobality gives a supported
slice where `gᵢ` differs from the interpolant `h*`; line consistency forces
agreement at the sampled `u`, and `Preliminaries.polynomialAgreement_avg_le_mdq`
bounds that agreement probability. -/
private lemma lineConsistentIndicator_probability_le_mdq
    (params : Parameters) [FieldModel params.q]
    {k : ℕ}
    (xs : PointTuple params k)
    (hxs : Function.Injective xs)
    (gs : GHatTupleOutcome params k)
    (hEligible : InterpolationEligible params gs) :
    avgOver (uniformDistribution (Point params)) (fun u =>
        if (¬ IsGloballyConsistent params xs gs) ∧
            ∃ f : AxisLinePolynomial params.next,
              ¬ (∃ i : Fin k, ∃ hiSome : (gs i).isSome = true,
                ((gs i).get hiSome) u ≠ f (xs i)) then
          (1 : Error)
        else 0) ≤
      ((params.m * params.d : ℕ) : Error) / (params.q : Error) := by
  classical
  let δ : Error := ((params.m * params.d : ℕ) : Error) / (params.q : Error)
  have hδ_nonneg : 0 ≤ δ := by
    dsimp [δ]
    positivity
  by_cases hGlobal : IsGloballyConsistent params xs gs
  · calc
      avgOver (uniformDistribution (Point params)) (fun u =>
          if (¬ IsGloballyConsistent params xs gs) ∧
              ∃ f : AxisLinePolynomial params.next,
                ¬ (∃ i : Fin k, ∃ hiSome : (gs i).isSome = true,
                  ((gs i).get hiSome) u ≠ f (xs i)) then
            (1 : Error)
          else 0) = 0 := by
            simp [hGlobal, avgOver_zero]
      _ ≤ ((params.m * params.d : ℕ) : Error) / (params.q : Error) := hδ_nonneg
  · rcases nonglobal_gives_slice_mismatch_against_interpolant params xs gs hGlobal with
      ⟨i, hiSome, hsliceNe⟩
    let hStarSlice : Polynomial params :=
      Polynomial.restrictAtHeight params (interpolateCompletedSlices params k xs gs) (xs i)
    have hneq : (gs i).get hiSome ≠ hStarSlice := by
      intro hEq
      exact hsliceNe (by simpa [hStarSlice] using hEq.symm)
    have hpoint : ∀ u : Point params,
        (if (¬ IsGloballyConsistent params xs gs) ∧
            ∃ f : AxisLinePolynomial params.next,
              ¬ (∃ j : Fin k, ∃ hjSome : (gs j).isSome = true,
                ((gs j).get hjSome) u ≠ f (xs j)) then
          (1 : Error)
        else 0) ≤
          if ((gs i).get hiSome) u = hStarSlice u then (1 : Error) else 0 := by
      intro u
      by_cases hCons : (¬ IsGloballyConsistent params xs gs) ∧
          ∃ f : AxisLinePolynomial params.next,
            ¬ (∃ j : Fin k, ∃ hjSome : (gs j).isSome = true,
              ((gs j).get hjSome) u ≠ f (xs j))
      · rcases hCons.2 with ⟨f, hNoMismatch⟩
        have hLine := tupleInterpolatedVerticalLine_eq_of_no_supported_mismatch
          params u xs hxs gs hEligible f hNoMismatch
        have htupleEval :
            tupleInterpolatedVerticalLine params u xs gs (xs i) = hStarSlice u := by
          dsimp [hStarSlice]
          simpa [tupleInterpolatedVerticalLine] using
            restrictToVerticalLine_eval_eq_restrictAtHeight_eval
              params (interpolateCompletedSlices params k xs gs) u (xs i)
        have hsliceEq : ((gs i).get hiSome) u = hStarSlice u := by
          have hnotNe : ¬ ((gs i).get hiSome) u ≠ f (xs i) := by
            intro hne
            exact hNoMismatch ⟨i, hiSome, hne⟩
          have hgf : ((gs i).get hiSome) u = f (xs i) := by
            by_contra hne
            exact hnotNe hne
          exact hgf.trans
            ((congrArg (fun line : AxisLinePolynomial params.next => line (xs i))
              hLine.symm).trans htupleEval)
        rw [if_pos hCons, if_pos hsliceEq]
      · rw [if_neg hCons]
        by_cases hEq : ((gs i).get hiSome) u = hStarSlice u <;> simp [hEq]
    calc
      avgOver (uniformDistribution (Point params)) (fun u =>
          if (¬ IsGloballyConsistent params xs gs) ∧
              ∃ f : AxisLinePolynomial params.next,
                ¬ (∃ j : Fin k, ∃ hjSome : (gs j).isSome = true,
                  ((gs j).get hjSome) u ≠ f (xs j)) then
            (1 : Error)
          else 0)
        ≤ avgOver (uniformDistribution (Point params)) (fun u =>
            if ((gs i).get hiSome) u = hStarSlice u then (1 : Error) else 0) := by
            exact avgOver_mono _ _ _ hpoint
      _ ≤ δ := by
            simpa [δ, hStarSlice] using
              Preliminaries.polynomialAgreement_avg_le_mdq
                params ((gs i).get hiSome) hStarSlice hneq

/-- Expand an averaged restricted lifted submeasurement into per-outcome masses
weighted by the probability of the restricting predicate. -/
private lemma avgOver_subMeasMass_restrict_liftLeft_eq_sum_coeff
    {Question Outcome : Type*} [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (𝒟 : Distribution Question)
    (A : SubMeas Outcome ι)
    (P : Question → Outcome → Prop) [∀ q, DecidablePred (P q)] :
    avgOver 𝒟 (fun q => subMeasMass ψ ((restrictSubMeas A (P q)).liftLeft)) =
      ∑ a : Outcome,
        avgOver 𝒟 (fun q => if P q a then (1 : Error) else 0) *
          ev ψ (leftTensor (ι₂ := ι) (A.outcome a)) := by
  classical
  calc
    avgOver 𝒟 (fun q => subMeasMass ψ ((restrictSubMeas A (P q)).liftLeft))
      = avgOver 𝒟 (fun q =>
          ∑ a : Outcome,
            if P q a then ev ψ (leftTensor (ι₂ := ι) (A.outcome a)) else 0) := by
          apply avgOver_congr
          intro q
          unfold subMeasMass SubMeas.liftLeft restrictSubMeas
          rw [mkLeftPlacedSubMeas_total]
          rw [← leftTensor_finset_sum (ι₂ := ι)
            (Finset.univ.filter (P q)) (fun a => A.outcome a)]
          rw [ev_finset_sum]
          rw [Finset.sum_filter]
    _ = ∑ a : Outcome,
        avgOver 𝒟 (fun q =>
          if P q a then ev ψ (leftTensor (ι₂ := ι) (A.outcome a)) else 0) :=
          avgOver_sum 𝒟 (fun q a =>
            if P q a then ev ψ (leftTensor (ι₂ := ι) (A.outcome a)) else 0)
    _ = ∑ a : Outcome,
        avgOver 𝒟 (fun q => (if P q a then (1 : Error) else 0) *
          ev ψ (leftTensor (ι₂ := ι) (A.outcome a))) := by
          refine Finset.sum_congr rfl ?_
          intro a _
          apply avgOver_congr
          intro q
          by_cases hp : P q a <;> simp [hp]
    _ = ∑ a : Outcome,
        avgOver 𝒟 (fun q => if P q a then (1 : Error) else 0) *
          ev ψ (leftTensor (ι₂ := ι) (A.outcome a)) := by
          refine Finset.sum_congr rfl ?_
          intro a _
          rw [avgOver_mul_const]

/-- Fixed-distinct-tuple form of the line-consistent Schwartz--Zippel bound. -/
private lemma lineConsistentIndicatorLocal_avg_le_mdq
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) {k : ℕ}
    (xs : PointTuple params k)
    (hxs : Function.Injective xs) :
    avgOver (uniformDistribution (Point params)) (fun u =>
        overAllOutcomesLineConsistentIndicatorLocal params strategy family u xs) ≤
      ((params.m * params.d : ℕ) : Error) / (params.q : Error) := by
  classical
  let δ : Error := ((params.m * params.d : ℕ) : Error) / (params.q : Error)
  let A := interpolationEligibleSandwichFamily params family k xs
  let P : Point params → GHatTupleOutcome params k → Prop := fun u gs =>
    (¬ IsGloballyConsistent params xs gs) ∧
      ∃ f : AxisLinePolynomial params.next,
        ¬ (∃ i : Fin k, ∃ hiSome : (gs i).isSome = true,
          ((gs i).get hiSome) u ≠ f (xs i))
  have hδ_nonneg : 0 ≤ δ := by
    dsimp [δ]
    positivity
  have hmass_nonneg : ∀ gs : GHatTupleOutcome params k,
      0 ≤ ev strategy.state (leftTensor (ι₂ := ι) (A.outcome gs)) := by
    intro gs
    exact ev_nonneg_of_psd strategy.state _ <|
      leftTensor_nonneg (ι₂ := ι) (A.outcome_pos gs)
  calc
    avgOver (uniformDistribution (Point params)) (fun u =>
        overAllOutcomesLineConsistentIndicatorLocal params strategy family u xs)
      = ∑ gs : GHatTupleOutcome params k,
          avgOver (uniformDistribution (Point params))
            (fun u => if P u gs then (1 : Error) else 0) *
            ev strategy.state (leftTensor (ι₂ := ι) (A.outcome gs)) := by
          unfold overAllOutcomesLineConsistentIndicatorLocal
          dsimp [A, P]
          exact avgOver_subMeasMass_restrict_liftLeft_eq_sum_coeff
            strategy.state (uniformDistribution (Point params)) A P
    _ ≤ ∑ gs : GHatTupleOutcome params k,
          δ * ev strategy.state (leftTensor (ι₂ := ι) (A.outcome gs)) := by
          refine Finset.sum_le_sum ?_
          intro gs _
          by_cases hEligible : InterpolationEligible params gs
          · have hprob := lineConsistentIndicator_probability_le_mdq
              params xs hxs gs hEligible
            exact mul_le_mul_of_nonneg_right (by simpa [P, δ] using hprob)
              (hmass_nonneg gs)
          · have hAout : A.outcome gs = 0 := by
              simp [A, interpolationEligibleSandwichFamily, restrictSubMeas, hEligible]
            simp [hAout, leftTensor, ev]
    _ = δ * ∑ gs : GHatTupleOutcome params k,
          ev strategy.state (leftTensor (ι₂ := ι) (A.outcome gs)) := by
          rw [Finset.mul_sum]
    _ = δ * subMeasMass strategy.state A.liftLeft := by
          change δ * ∑ gs : GHatTupleOutcome params k,
              ev strategy.state (leftTensor (ι₂ := ι) (A.outcome gs)) =
            δ * ev strategy.state (leftTensor (ι₂ := ι) A.total)
          rw [ev_leftTensor_total_eq_sum_outcome strategy.state A]
    _ ≤ δ * 1 := by
          exact mul_le_mul_of_nonneg_left
            (eligibleMass_le_one params strategy family xs) hδ_nonneg
    _ = ((params.m * params.d : ℕ) : Error) / (params.q : Error) := by
          simp [δ]

/-- The line-consistent Schwartz--Zippel aggregation after the insertion and
bad-line finite-sum split.

Paper anchor: `ld-pasting.tex` lines 1235--1275.  For every distinct tuple `xs`,
interpolation-eligible nonglobal outcome `gs`, and line-consistent answer `f`, the
paper chooses the interpolant `h*`; nonglobality gives a supported coordinate
where `gᵢ ≠ h*|_{xsᵢ}`, and Schwartz--Zippel bounds the probability over `u` that
this disagreement vanishes by `md/q`. -/
private lemma overAllOutcomes_distinct_lineConsistent_indicator_mass_le_mdq
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) (k : ℕ) :
    overAllOutcomesDistinctLineConsistentIndicatorMass params strategy family k ≤
      ((params.m * params.d : ℕ) : Error) / (params.q : Error) := by
  classical
  let δ : Error := ((params.m * params.d : ℕ) : Error) / (params.q : Error)
  have hδ_nonneg : 0 ≤ δ := by
    dsimp [δ]
    positivity
  unfold overAllOutcomesDistinctLineConsistentIndicatorMass
  rw [avgOver_comm (uniformDistribution (Point params))
    (distinctTupleDistribution params k)
    (fun u xs => overAllOutcomesLineConsistentIndicatorLocal params strategy family u xs)]
  calc
    avgOver (distinctTupleDistribution params k) (fun xs =>
        avgOver (uniformDistribution (Point params)) (fun u =>
          overAllOutcomesLineConsistentIndicatorLocal params strategy family u xs))
      ≤ avgOver (distinctTupleDistribution params k) (fun _ => δ) := by
          refine avgOver_mono_on_support (distinctTupleDistribution params k) _ _ ?_
          intro xs hxs_mem
          have hxs : Function.Injective xs := by
            simpa [distinctTupleDistribution] using hxs_mem
          simpa [δ] using
            lineConsistentIndicatorLocal_avg_le_mdq params strategy family xs hxs
    _ ≤ δ := by
          unfold avgOver
          calc
            ∑ xs ∈ (distinctTupleDistribution params k).support,
                (distinctTupleDistribution params k).weight xs * δ
              = (∑ xs ∈ (distinctTupleDistribution params k).support,
                  (distinctTupleDistribution params k).weight xs) * δ := by
                  rw [← Finset.sum_mul]
            _ ≤ 1 * δ := by
                  exact mul_le_mul_of_nonneg_right
                    (distinctTupleDistribution_weight_sum_le_one params k) hδ_nonneg
            _ = δ := by ring
    _ = ((params.m * params.d : ℕ) : Error) / (params.q : Error) := by
          rfl

/-- The local finite-sum/SZ comparison after the one-point line-mismatch
aggregation has been separated off.

The insertion and finite-sum split from `ld-pasting.tex` lines 1174--1228 are
proved by `overAllOutcomes_distinct_nonglobal_mass_le_bad_line_mass_add_lineConsistent`.
The line-consistent remainder is exactly the Schwartz--Zippel aggregation proved
by `overAllOutcomes_distinct_lineConsistent_indicator_mass_le_mdq`, corresponding
to lines 1235--1275. -/
private lemma overAllOutcomes_distinct_nonglobal_mass_le_bad_line_mass_add_mdq
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) (k : ℕ) :
    overAllOutcomesDistinctNonglobalMass params strategy family k ≤
      overAllOutcomesDistinctBadLineMass params strategy family k +
        ((params.m * params.d : ℕ) : Error) / (params.q : Error) := by
  have hsplit :=
    overAllOutcomes_distinct_nonglobal_mass_le_bad_line_mass_add_lineConsistent
      params strategy family k
  have hindicator := lineConsistentNonglobalMass_le_indicatorMass
    params strategy family k
  have hsz :=
    overAllOutcomes_distinct_lineConsistent_indicator_mass_le_mdq
      params strategy family k
  linarith

/-- If the distinct nonglobal mass is bounded by the paper's local
`k·ν₅ + k²/q + md/q` comparison, then the reverse half of
`lem:over-all-outcomes` follows.

The remaining hypothesis is exactly the content of `ld-pasting.tex` lines
1174--1275: insert the line measurement, pay the one-point line consistency
bound to add the consistency indicator, and use Schwartz--Zippel for the
indicator term. -/
private lemma overAllOutcomes_reverse_mass_bound_of_nonglobal_mass_bound
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (eps delta gamma zeta : Error) (k : ℕ)
    (hd : 0 < params.d)
    (hdq_le : params.d ≤ params.q)
    (hkEligible : params.d + 1 ≤ k)
    (heps_nonneg : 0 ≤ eps)
    (hdelta_nonneg : 0 ≤ delta)
    (hgamma_nonneg : 0 ≤ gamma)
    (hzeta_nonneg : 0 ≤ zeta)
    (hnonglobal :
      overAllOutcomesDistinctNonglobalMass params strategy family k ≤
        hBConsistencyError params eps delta gamma zeta k +
          ((params.m * params.d : ℕ) : Error) / (params.q : Error)) :
    overAllOutcomesExpansionMass params strategy family k -
        overAllOutcomesPastedMass params strategy family k ≤
      overAllOutcomesError params eps delta gamma zeta k := by
  have hswap := avgOver_uniform_eligibleMass_le_distinct_add_dnoteq
    params strategy family k
  have hsplit := avgOver_distinct_eligibleMass_eq_global_add_nonglobal
    params strategy family k
  rw [overAllOutcomesExpansionMass_eq_avg_uniform_eligible,
    overAllOutcomesPastedMass_eq_avg_distinct_global]
  have hbound := hBConsistencyError_add_mdq_add_dnoteq_le_overAllOutcomesError
    params eps delta gamma zeta k hd hdq_le hkEligible
    heps_nonneg hdelta_nonneg hgamma_nonneg hzeta_nonneg
  linarith

/-- The paper-local nonglobal mass comparison after the algebraic reductions.

The one-point line-comparison aggregation from `ld-pasting.tex` lines 1186--1202
is proved by `overAllOutcomes_distinct_bad_line_mass_le_hBConsistencyError`, and
the remaining insertion/Schwartz--Zippel estimate is
`overAllOutcomes_distinct_nonglobal_mass_le_bad_line_mass_add_mdq`. -/
private lemma overAllOutcomes_distinct_nonglobal_mass_bound
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (eps delta gamma zeta : Error) (k : ℕ)
    (hd : 0 < params.d)
    (heps_nonneg : 0 ≤ eps)
    (hdelta_nonneg : 0 ≤ delta)
    (hgamma_nonneg : 0 ≤ gamma)
    (hzeta_nonneg : 0 ≤ zeta)
    (hline : ∀ i : ℕ, i < k →
      LdSandwichLineOnePointStatement params strategy family
        eps delta gamma zeta k i) :
    overAllOutcomesDistinctNonglobalMass params strategy family k ≤
      hBConsistencyError params eps delta gamma zeta k +
        ((params.m * params.d : ℕ) : Error) / (params.q : Error) := by
  have hlocal :=
    overAllOutcomes_distinct_nonglobal_mass_le_bad_line_mass_add_mdq
      params strategy family k
  have hbad :=
    overAllOutcomes_distinct_bad_line_mass_le_hBConsistencyError
      params strategy family eps delta gamma zeta k hd
      heps_nonneg hdelta_nonneg hgamma_nonneg hzeta_nonneg hline
  linarith

/-- Reduction of `lem:over-all-outcomes` to a reverse mass comparison.

The forward direction
`overAllOutcomesPastedMass - overAllOutcomesExpansionMass` is now discharged by
expanding the pasted mass over distinct tuples, forgetting global consistency,
and paying only `ldDnoteq`.  The reverse loss
`overAllOutcomesExpansionMass - overAllOutcomesPastedMass` is the part of
`ld-pasting.tex` supplied below by the completed `ldSandwichLineOnePoint`
aggregation. -/
private lemma overAllOutcomes_of_reverse_mass_bound
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (eps delta gamma zeta : Error) (k : ℕ)
    (hd : 0 < params.d)
    (heps_nonneg : 0 ≤ eps)
    (hdelta_nonneg : 0 ≤ delta)
    (hgamma_nonneg : 0 ≤ gamma)
    (hzeta_nonneg : 0 ≤ zeta)
    (hreverse :
      overAllOutcomesExpansionMass params strategy family k -
          overAllOutcomesPastedMass params strategy family k ≤
        overAllOutcomesError params eps delta gamma zeta k) :
    OverAllOutcomesStatement params strategy family eps delta gamma zeta k := by
  refine ⟨?_⟩
  have hforward_dnoteq := overAllOutcomes_pasted_sub_expansion_le_dnoteq
    params strategy family k
  have hforward :
      overAllOutcomesPastedMass params strategy family k -
          overAllOutcomesExpansionMass params strategy family k ≤
        overAllOutcomesError params eps delta gamma zeta k := by
    exact le_trans hforward_dnoteq
      (dnoteq_term_le_overAllOutcomesError params eps delta gamma zeta k hd
        heps_nonneg hdelta_nonneg hgamma_nonneg hzeta_nonneg)
  exact abs_le.mpr ⟨by linarith, hforward⟩









end MIPStarRE.LDT.Pasting

end

end LIDT

open LIDT
/-!
# Section 12 pasting: over all outcomes — Schwartz–Zippel bounds and final assembly

Schwartz–Zippel aggregation, the line-consistent indicator bound, and the final chained
assembly of `lem:over-all-outcomes`.

## References

- `references/ldt-paper/ld-pasting.tex`
- `blueprint/src/chapter/ch09_pasting.tex`
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
    (strategy : _root_.LIDT.MIPStarRE.LDT.SymStrat params.next ι)
    (eps delta gamma zeta : _root_.LIDT.MIPStarRE.LDT.Error)
    (heps_nonneg : 0 ≤ eps)
    (hdelta_nonneg : 0 ≤ delta)
    (hgamma_nonneg : 0 ≤ gamma)
    (hzeta_nonneg : 0 ≤ zeta)
    (hdq_le : params.d ≤ params.q)
    (hd : 0 < params.d)
    (family : _root_.LIDT.MIPStarRE.LDT.IdxPolyFamily params ι)
    (k : ℕ)
    (hline : ∀ i : ℕ, i < k →
      _root_.LIDT.MIPStarRE.LDT.Pasting.LdSandwichLineOnePointStatement params strategy family
        eps delta gamma zeta k i) :
    _root_.LIDT.MIPStarRE.LDT.Pasting.OverAllOutcomesStatement params strategy family eps delta gamma zeta k := by
  have hreverse :
      _root_.LIDT.MIPStarRE.LDT.Pasting.overAllOutcomesExpansionMass params strategy family k -
          _root_.LIDT.MIPStarRE.LDT.Pasting.overAllOutcomesPastedMass params strategy family k ≤
        _root_.LIDT.MIPStarRE.LDT.Pasting.overAllOutcomesError params eps delta gamma zeta k := by
    by_cases hkEligible : params.d + 1 ≤ k
    · have hnonglobal := overAllOutcomes_distinct_nonglobal_mass_bound
        params strategy family eps delta gamma zeta k hd
        heps_nonneg hdelta_nonneg hgamma_nonneg hzeta_nonneg hline
      exact overAllOutcomes_reverse_mass_bound_of_nonglobal_mass_bound
        params strategy family eps delta gamma zeta k hd hdq_le hkEligible
        heps_nonneg hdelta_nonneg hgamma_nonneg hzeta_nonneg hnonglobal
    · exact _root_.LIDT.MIPStarRE.LDT.Pasting.overAllOutcomes_reverse_mass_bound_of_not_d_add_one_le
        params strategy family eps delta gamma zeta k hkEligible
        heps_nonneg hdelta_nonneg hgamma_nonneg hzeta_nonneg
  exact overAllOutcomes_of_reverse_mass_bound params strategy family
    eps delta gamma zeta k hd heps_nonneg hdelta_nonneg hgamma_nonneg
    hzeta_nonneg hreverse
