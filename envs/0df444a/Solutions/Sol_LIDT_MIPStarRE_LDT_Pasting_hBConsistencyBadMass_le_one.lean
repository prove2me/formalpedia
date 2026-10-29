-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Pasting.hBConsistencyBadMass_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T16:29:11.935313+00:00
-- url     : https://prove2.me/submissions/e3ac61a5-2825-4906-b678-ba9618e3ce86

-- Generated proof for MIPStarRE.LDT.Pasting.hBConsistencyBadMass_le_one.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LineInterpolation_BadLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LineInterpolation_BadMass
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LineInterpolation_Core
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

end LIDT

open LIDT
/-!
# Line interpolation: bad-mass comparison

Main bad-mass comparison lemmas: sandwich mismatch sums, `qBipartiteConsDefect`
equality via single-outcome measurements, `hBConsistencyBadMass`, line-point
defect bounds, and `pastedInterpolation_verticalLine_defect_le_badMass`.

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
    (family : _root_.LIDT.MIPStarRE.LDT.IdxPolyFamily params ι)
    {k : ℕ} (u : _root_.LIDT.MIPStarRE.LDT.Point params) (xs : _root_.LIDT.MIPStarRE.LDT.PointTuple params k) :
    _root_.LIDT.MIPStarRE.LDT.Pasting.hBConsistencyBadMass params strategy family u xs ≤ 1 := by
  let T : _root_.LIDT.MIPStarRE.Quantum.Op ι := (_root_.LIDT.MIPStarRE.LDT.Pasting.interpolationEligibleSandwichFamily params family k xs).total
  let L : _root_.LIDT.MIPStarRE.LDT.AxisLinePolynomial params.next → _root_.LIDT.MIPStarRE.Quantum.Op ι := fun f =>
    ∑ gs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params k,
      if ∃ i : Fin k, ∃ hiSome : (gs i).isSome = true, ((gs i).get hiSome) u ≠ f (xs i) then
        (_root_.LIDT.MIPStarRE.LDT.Pasting.interpolationEligibleSandwichFamily params family k xs).outcome gs
      else 0
  have hLle : ∀ f : _root_.LIDT.MIPStarRE.LDT.AxisLinePolynomial params.next, L f ≤ T := by
    intro f
    calc
      L f ≤ ∑ gs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params k,
          (_root_.LIDT.MIPStarRE.LDT.Pasting.interpolationEligibleSandwichFamily params family k xs).outcome gs := by
            unfold L
            refine Finset.sum_le_sum ?_
            intro gs _
            by_cases hbad : ∃ i : Fin k, ∃ hiSome : (gs i).isSome = true,
                ((gs i).get hiSome) u ≠ f (xs i)
            · simp [hbad]
            · simp [hbad, (_root_.LIDT.MIPStarRE.LDT.Pasting.interpolationEligibleSandwichFamily params family k xs).outcome_pos gs]
      _ = T := by
            simpa [T] using (_root_.LIDT.MIPStarRE.LDT.Pasting.interpolationEligibleSandwichFamily params family k xs).sum_eq_total
  have hsum_le :
      _root_.LIDT.MIPStarRE.LDT.Pasting.hBConsistencyBadMass params strategy family u xs ≤
        ∑ f : _root_.LIDT.MIPStarRE.LDT.AxisLinePolynomial params.next,
          _root_.LIDT.MIPStarRE.LDT.ev strategy.state (_root_.LIDT.MIPStarRE.LDT.opTensor T (
              (_root_.LIDT.MIPStarRE.LDT.Pasting.verticalLineMeasurementFamily params strategy u).outcome f)) := by
    unfold _root_.LIDT.MIPStarRE.LDT.Pasting.hBConsistencyBadMass
    refine Finset.sum_le_sum ?_
    intro f _
    exact _root_.LIDT.MIPStarRE.LDT.ev_mono strategy.state _ _ <|
      _root_.LIDT.MIPStarRE.LDT.opTensor_mono_left (hLle f) ((_root_.LIDT.MIPStarRE.LDT.Pasting.verticalLineMeasurementFamily params strategy u).outcome_pos f)
  have htotal_eq_one : (_root_.LIDT.MIPStarRE.LDT.Pasting.verticalLineMeasurementFamily params strategy u).total = 1 := by
    let ℓ : _root_.LIDT.MIPStarRE.LDT.AxisParallelLine params.next :=
      { base := _root_.LIDT.MIPStarRE.LDT.appendPoint params u _root_.LIDT.MIPStarRE.LDT.zeroCoord
        direction := _root_.LIDT.MIPStarRE.LDT.lastCoord params }
    simpa [_root_.LIDT.MIPStarRE.LDT.Pasting.verticalLineMeasurementFamily, ℓ] using (strategy.axisParallelMeasurement ℓ).total_eq_one
  calc
    _root_.LIDT.MIPStarRE.LDT.Pasting.hBConsistencyBadMass params strategy family u xs
      ≤ ∑ f : _root_.LIDT.MIPStarRE.LDT.AxisLinePolynomial params.next,
          _root_.LIDT.MIPStarRE.LDT.ev strategy.state (_root_.LIDT.MIPStarRE.LDT.opTensor T (
              (_root_.LIDT.MIPStarRE.LDT.Pasting.verticalLineMeasurementFamily params strategy u).outcome f)) := hsum_le
    _ = _root_.LIDT.MIPStarRE.LDT.ev strategy.state (_root_.LIDT.MIPStarRE.LDT.opTensor T (_root_.LIDT.MIPStarRE.LDT.Pasting.verticalLineMeasurementFamily params strategy u).total) := by
          rw [← _root_.LIDT.MIPStarRE.LDT.ev_finset_sum, ← _root_.LIDT.MIPStarRE.LDT.opTensor_sum_right_finset]
          rw [(_root_.LIDT.MIPStarRE.LDT.Pasting.verticalLineMeasurementFamily params strategy u).sum_eq_total]
    _ = _root_.LIDT.MIPStarRE.LDT.ev strategy.state (_root_.LIDT.MIPStarRE.LDT.opTensor T (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι)) := by rw [htotal_eq_one]
    _ ≤ 1 := by
          have hTle : T ≤ 1 := by simpa [T] using (
              _root_.LIDT.MIPStarRE.LDT.Pasting.interpolationEligibleSandwichFamily params family k xs).total_le_one
          have hop : _root_.LIDT.MIPStarRE.LDT.opTensor T (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) ≤ 1 := by
            simpa [_root_.LIDT.MIPStarRE.LDT.opTensor, _root_.LIDT.MIPStarRE.LDT.leftTensor] using _root_.LIDT.MIPStarRE.LDT.leftTensor_le_one (ι₂ := ι) (A := T) hTle
          simpa [_root_.LIDT.MIPStarRE.LDT.ev_one_of_isNormalized strategy.state strategy.isNormalized] using
            (_root_.LIDT.MIPStarRE.LDT.ev_mono strategy.state _ _ hop)
