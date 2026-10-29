-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Pasting.overAllOutcomes_distinct_nonglobal_mass_le_bad_line_mass_add_lineConsistent
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T16:40:01.159985+00:00
-- url     : https://prove2.me/submissions/c518ec6c-32f3-4611-bd3b-676ca52c3d68

-- Generated proof for MIPStarRE.LDT.Pasting.overAllOutcomes_distinct_nonglobal_mass_le_bad_line_mass_add_lineConsistent.
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











/-- Inserting the vertical-line measurement leaves the local nonglobal mass
unchanged. -/
private lemma nonglobal_mass_eq_inserted_vertical_measurement
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) {k : ℕ}
    (u : Point params) (xs : PointTuple params k) :
    subMeasMass strategy.state
        ((restrictSubMeas (interpolationEligibleSandwichFamily params family k xs)
          (fun gs => ¬ IsGloballyConsistent params xs gs)).liftLeft) =
      overAllOutcomesNonglobalInsertedMassLocal params strategy family u xs := by
  classical
  let A := interpolationEligibleSandwichFamily params family k xs
  let B := verticalLineMeasurementFamily params strategy u
  let T : MIPStarRE.Quantum.Op ι :=
    ∑ gs : GHatTupleOutcome params k,
      if IsGloballyConsistent params xs gs then 0 else A.outcome gs
  have hT :
      (restrictSubMeas A (fun gs => ¬ IsGloballyConsistent params xs gs)).total = T := by
    change (∑ gs ∈ (Finset.univ.filter
        (fun gs : GHatTupleOutcome params k => ¬ IsGloballyConsistent params xs gs)),
        A.outcome gs) = T
    rw [Finset.sum_filter]
    dsimp [T]
    refine Finset.sum_congr rfl ?_
    intro gs _
    by_cases hglobal : IsGloballyConsistent params xs gs <;> simp [hglobal]
  have hBtotal : B.total = 1 := by
    simpa [B] using verticalLineMeasurementFamily_total_eq_one params strategy u
  calc
    subMeasMass strategy.state
        ((restrictSubMeas (interpolationEligibleSandwichFamily params family k xs)
          (fun gs => ¬ IsGloballyConsistent params xs gs)).liftLeft)
        = ev strategy.state (opTensor T (1 : MIPStarRE.Quantum.Op ι)) := by
            simp [subMeasMass, SubMeas.liftLeft, A, T, hT, leftTensor, opTensor]
    _ = ev strategy.state (opTensor T B.total) := by rw [hBtotal]
    _ = ev strategy.state (opTensor T (∑ f : AxisLinePolynomial params.next, B.outcome f)) := by
            rw [B.sum_eq_total]
    _ = ev strategy.state (∑ f : AxisLinePolynomial params.next, opTensor T (B.outcome f)) := by
            rw [opTensor_sum_right_finset]
    _ = overAllOutcomesNonglobalInsertedMassLocal params strategy family u xs := by
            rw [ev_finset_sum]
            simp [overAllOutcomesNonglobalInsertedMassLocal, A, B, T]

/-- Pointwise split: after inserting the vertical-line measurement, every nonglobal
outcome either contributes to the already-paid bad-line event or to the
line-consistent residual. -/
private lemma nonglobal_insertedMass_le_badLineMass_add_lineConsistentLocal
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) {k : ℕ}
    (u : Point params) (xs : PointTuple params k) :
    overAllOutcomesNonglobalInsertedMassLocal params strategy family u xs ≤
      hBConsistencyBadMass params strategy family u xs +
        overAllOutcomesLineConsistentNonglobalLocal params strategy family u xs := by
  classical
  unfold overAllOutcomesNonglobalInsertedMassLocal hBConsistencyBadMass
    overAllOutcomesLineConsistentNonglobalLocal
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum ?_
  intro f _
  rw [← ev_add]
  apply ev_mono strategy.state _ _
  rw [← opTensor_add_left_local]
  apply opTensor_mono_left
  · rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum ?_
    intro gs _
    by_cases hglobal : IsGloballyConsistent params xs gs
    · by_cases hbad : ∃ i : Fin k, ∃ hiSome : (gs i).isSome = true,
          ((gs i).get hiSome) u ≠ f (xs i)
      · have hnonneg : 0 ≤
            (interpolationEligibleSandwichFamily params family k xs).outcome gs :=
          (interpolationEligibleSandwichFamily params family k xs).outcome_pos gs
        simp [hglobal, hbad, hnonneg]
      · simp [hglobal, hbad]
    · by_cases hbad : ∃ i : Fin k, ∃ hiSome : (gs i).isSome = true,
          ((gs i).get hiSome) u ≠ f (xs i)
      · simp [hglobal, hbad]
      · simp [hglobal, hbad]
  · exact (verticalLineMeasurementFamily params strategy u).outcome_pos f







end MIPStarRE.LDT.Pasting

end

end LIDT

open LIDT
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

open LIDT.MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem solution
    (params : _root_.LIDT.MIPStarRE.LDT.Parameters) [_root_.LIDT.MIPStarRE.LDT.FieldModel params.q]
    (strategy : _root_.LIDT.MIPStarRE.LDT.SymStrat params.next ι)
    (family : _root_.LIDT.MIPStarRE.LDT.IdxPolyFamily params ι) (k : ℕ) :
    _root_.LIDT.MIPStarRE.LDT.Pasting.overAllOutcomesDistinctNonglobalMass params strategy family k ≤
      _root_.LIDT.MIPStarRE.LDT.Pasting.overAllOutcomesDistinctBadLineMass params strategy family k +
        _root_.LIDT.MIPStarRE.LDT.Pasting.overAllOutcomesDistinctLineConsistentNonglobalMass params strategy family k := by
  classical
  let inserted : _root_.LIDT.MIPStarRE.LDT.Point params → _root_.LIDT.MIPStarRE.LDT.PointTuple params k → _root_.LIDT.MIPStarRE.LDT.Error := fun u xs =>
    overAllOutcomesNonglobalInsertedMassLocal params strategy family u xs
  let bad : _root_.LIDT.MIPStarRE.LDT.Point params → _root_.LIDT.MIPStarRE.LDT.PointTuple params k → _root_.LIDT.MIPStarRE.LDT.Error := fun u xs =>
    _root_.LIDT.MIPStarRE.LDT.Pasting.hBConsistencyBadMass params strategy family u xs
  let consistent : _root_.LIDT.MIPStarRE.LDT.Point params → _root_.LIDT.MIPStarRE.LDT.PointTuple params k → _root_.LIDT.MIPStarRE.LDT.Error := fun u xs =>
    _root_.LIDT.MIPStarRE.LDT.Pasting.overAllOutcomesLineConsistentNonglobalLocal params strategy family u xs
  have hrewrite :
      _root_.LIDT.MIPStarRE.LDT.Pasting.overAllOutcomesDistinctNonglobalMass params strategy family k =
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params)) (fun u =>
          _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.Pasting.distinctTupleDistribution params k) (fun xs => inserted u xs)) := by
    calc
      _root_.LIDT.MIPStarRE.LDT.Pasting.overAllOutcomesDistinctNonglobalMass params strategy family k
          = _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.Pasting.distinctTupleDistribution params k) (fun xs =>
              _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params)) (fun u => inserted u xs)) := by
              unfold _root_.LIDT.MIPStarRE.LDT.Pasting.overAllOutcomesDistinctNonglobalMass
              apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
              intro xs
              calc
                _root_.LIDT.MIPStarRE.LDT.subMeasMass strategy.state
                    ((_root_.LIDT.MIPStarRE.LDT.Pasting.restrictSubMeas (_root_.LIDT.MIPStarRE.LDT.Pasting.interpolationEligibleSandwichFamily params family k xs)
                      (fun gs => ¬ _root_.LIDT.MIPStarRE.LDT.Pasting.IsGloballyConsistent params xs gs)).liftLeft)
                    = _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params)) (fun _ : _root_.LIDT.MIPStarRE.LDT.Point params =>
                        _root_.LIDT.MIPStarRE.LDT.subMeasMass strategy.state
                          ((_root_.LIDT.MIPStarRE.LDT.Pasting.restrictSubMeas (_root_.LIDT.MIPStarRE.LDT.Pasting.interpolationEligibleSandwichFamily params family k xs)
                            (fun gs => ¬ _root_.LIDT.MIPStarRE.LDT.Pasting.IsGloballyConsistent params xs gs)).liftLeft)) := by
                        rw [_root_.LIDT.MIPStarRE.LDT.avgOver_uniform_const]
                _ = _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params)) (fun u => inserted u xs) := by
                        apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
                        intro u
                        exact nonglobal_mass_eq_inserted_vertical_measurement
                          params strategy family u xs
      _ = _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params)) (fun u =>
            _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.Pasting.distinctTupleDistribution params k) (fun xs => inserted u xs)) := by
            exact _root_.LIDT.MIPStarRE.LDT.avgOver_comm (_root_.LIDT.MIPStarRE.LDT.Pasting.distinctTupleDistribution params k)
              (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params)) (fun xs u => inserted u xs)
  rw [hrewrite]
  calc
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params)) (fun u =>
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.Pasting.distinctTupleDistribution params k) (fun xs => inserted u xs))
      ≤ _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params)) (fun u =>
          _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.Pasting.distinctTupleDistribution params k) (fun xs => bad u xs + consistent u xs)) := by
          apply _root_.LIDT.MIPStarRE.LDT.avgOver_mono
          intro u
          apply _root_.LIDT.MIPStarRE.LDT.avgOver_mono
          intro xs
          exact nonglobal_insertedMass_le_badLineMass_add_lineConsistentLocal
            params strategy family u xs
    _ = _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params)) (fun u =>
          _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.Pasting.distinctTupleDistribution params k) (fun xs => bad u xs) +
            _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.Pasting.distinctTupleDistribution params k) (fun xs => consistent u xs)) := by
          apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
          intro u
          rw [_root_.LIDT.MIPStarRE.LDT.avgOver_add]
    _ = _root_.LIDT.MIPStarRE.LDT.Pasting.overAllOutcomesDistinctBadLineMass params strategy family k +
          _root_.LIDT.MIPStarRE.LDT.Pasting.overAllOutcomesDistinctLineConsistentNonglobalMass params strategy family k := by
          rw [_root_.LIDT.MIPStarRE.LDT.avgOver_add]
          rfl
