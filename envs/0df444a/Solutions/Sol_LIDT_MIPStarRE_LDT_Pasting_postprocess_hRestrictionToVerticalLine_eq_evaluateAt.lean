-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Pasting.postprocess_hRestrictionToVerticalLine_eq_evaluateAt
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T16:48:09.697583+00:00
-- url     : https://prove2.me/submissions/ae80624a-b487-44aa-8251-421d7a9e0a82

-- Generated proof for MIPStarRE.LDT.Pasting.postprocess_hRestrictionToVerticalLine_eq_evaluateAt.
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
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_verticalLine_pointAt_appendPoint

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

/- Source helpers from MIPStarRE/LDT/Pasting/ComparisonLemmas/Common.lean. -/
/-!
# Section 12 pasting: comparison common helpers

Shared postprocessing, symmetry, distribution, boundedness, and arithmetic helpers for the Section
12 comparison lemmas.

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

lemma postprocess_postprocess
    {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (A : SubMeas α ι) (f : α → β) (g : β → γ) :
    postprocess (postprocess A f) g = postprocess A (g ∘ f) := by
  classical
  refine SubMeas.ext ?_ ?_
  · intro c
    simp [postprocess, Function.comp, Finset.sum_filter, Finset.sum_comm, eq_comm]
  · simp [postprocess_total]





















end MIPStarRE.LDT.Pasting

end

end LIDT

open LIDT
/-!
# Section 12 pasting: comparison common helpers

Shared postprocessing, symmetry, distribution, boundedness, and arithmetic helpers for the Section
12 comparison lemmas.

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
    (H : _root_.LIDT.MIPStarRE.LDT.SubMeas (_root_.LIDT.MIPStarRE.LDT.Polynomial params.next) ι) (u : _root_.LIDT.MIPStarRE.LDT.Point params.next) :
    _root_.LIDT.MIPStarRE.LDT.postprocess
      (_root_.LIDT.MIPStarRE.LDT.Pasting.hRestrictionToVerticalLine params H (_root_.LIDT.MIPStarRE.LDT.truncatePoint params u))
      (fun f => f (_root_.LIDT.MIPStarRE.LDT.pointHeight params u)) =
    _root_.LIDT.MIPStarRE.LDT.evaluateAt params.next u H := by
  let verticalLine : _root_.LIDT.MIPStarRE.LDT.AxisParallelLine params.next :=
    { base := _root_.LIDT.MIPStarRE.LDT.appendPoint params (_root_.LIDT.MIPStarRE.LDT.truncatePoint params u) _root_.LIDT.MIPStarRE.LDT.zeroCoord
      direction := _root_.LIDT.MIPStarRE.LDT.lastCoord params }
  rw [show _root_.LIDT.MIPStarRE.LDT.Pasting.hRestrictionToVerticalLine params H (_root_.LIDT.MIPStarRE.LDT.truncatePoint params u) =
      _root_.LIDT.MIPStarRE.LDT.postprocess H (fun h => _root_.LIDT.MIPStarRE.LDT.Polynomial.restrictToAxisParallelLine params.next h verticalLine) by
      rfl]
  rw [_root_.LIDT.MIPStarRE.LDT.Pasting.postprocess_postprocess]
  have happend : _root_.LIDT.MIPStarRE.LDT.appendPoint params (_root_.LIDT.MIPStarRE.LDT.truncatePoint params u) (_root_.LIDT.MIPStarRE.LDT.pointHeight params u) = u := by
    exact (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.pointNextEquiv params).left_inv u
  have hbase : _root_.LIDT.MIPStarRE.LDT.AxisParallelLine.pointAt verticalLine (_root_.LIDT.MIPStarRE.LDT.pointHeight params u) = u := by
    calc
      _root_.LIDT.MIPStarRE.LDT.AxisParallelLine.pointAt verticalLine (_root_.LIDT.MIPStarRE.LDT.pointHeight params u)
        = _root_.LIDT.MIPStarRE.LDT.appendPoint params (_root_.LIDT.MIPStarRE.LDT.truncatePoint params u) (_root_.LIDT.MIPStarRE.LDT.pointHeight params u) := by
            simpa [verticalLine] using
              _root_.LIDT.MIPStarRE.LDT.Pasting.verticalLine_pointAt_appendPoint params
                (_root_.LIDT.MIPStarRE.LDT.truncatePoint params u) (_root_.LIDT.MIPStarRE.LDT.pointHeight params u)
      _ = u := happend
  have hfun :
      (fun h =>
        (_root_.LIDT.MIPStarRE.LDT.Polynomial.restrictToAxisParallelLine params.next h verticalLine)
          (_root_.LIDT.MIPStarRE.LDT.pointHeight params u)) =
        fun h => h u := by
          funext h
          calc
            (_root_.LIDT.MIPStarRE.LDT.Polynomial.restrictToAxisParallelLine params.next h verticalLine)
                (_root_.LIDT.MIPStarRE.LDT.pointHeight params u)
              = h (_root_.LIDT.MIPStarRE.LDT.AxisParallelLine.pointAt verticalLine (_root_.LIDT.MIPStarRE.LDT.pointHeight params u)) :=
                  _root_.LIDT.MIPStarRE.LDT.Polynomial.restrictToAxisParallelLine_apply params.next h verticalLine
                    (_root_.LIDT.MIPStarRE.LDT.pointHeight params u)
            _ = h u := by simp [hbase]
  unfold _root_.LIDT.MIPStarRE.LDT.evaluateAt
  refine congrArg (_root_.LIDT.MIPStarRE.LDT.postprocess H) (funext fun h => ?_)
  change (_root_.LIDT.MIPStarRE.LDT.Polynomial.restrictToAxisParallelLine params.next h verticalLine) (_root_.LIDT.MIPStarRE.LDT.pointHeight params u)
      = h u
  exact congrFun hfun h
