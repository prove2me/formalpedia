-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Pasting.gHatRotatedHalfProduct_lastReverse_eq_conjTranspose_lastFront
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T16:29:11.733934+00:00
-- url     : https://prove2.me/submissions/e1c6bfd7-488a-4fda-9d5b-afe7d74497f2

-- Generated proof for MIPStarRE.LDT.Pasting.gHatRotatedHalfProduct_lastReverse_eq_conjTranspose_lastFront.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LdSandwichLineOnePoint_Endpoint
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LdSandwichLineOnePoint_EndpointEquivs
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
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_gHatHalfProduct_lastReverse_eq_conjTranspose

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
# Section 12 pasting: line one-point transport — prefix moved lemmas

Internal helper module; part of the file-split for `#1127`.

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
    (family : _root_.LIDT.MIPStarRE.LDT.IdxPolyFamily params ι) :
    ∀ i (xs : _root_.LIDT.MIPStarRE.LDT.PointTuple params (i + 1)) (gs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params (i + 1)),
      _root_.LIDT.MIPStarRE.LDT.Pasting.gHatRotatedHalfProductOutcomeOperator params family (i + 1)
          ((_root_.LIDT.MIPStarRE.LDT.Pasting.pointTupleLastReverseEquiv params i) xs)
          ((_root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleOutcomeLastReverseEquiv params i) gs) =
        (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family (i + 1)
          ((_root_.LIDT.MIPStarRE.LDT.Pasting.pointTupleLastFrontEquiv params i) xs)
          ((_root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleOutcomeLastFrontEquiv params i) gs))ᴴ := by
  intro i
  cases i with
  | zero =>
      intro xs gs
      have hhead :
          ((_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family (xs 0)).outcome (gs 0))ᴴ =
            (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family (xs 0)).outcome (gs 0) := by
        exact (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family (xs 0)).outcome_hermitian (gs 0)
      simp [_root_.LIDT.MIPStarRE.LDT.Pasting.pointTupleLastReverseEquiv, _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleOutcomeLastReverseEquiv,
        _root_.LIDT.MIPStarRE.LDT.Pasting.pointTupleLastFrontEquiv, _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleOutcomeLastFrontEquiv,
        _root_.LIDT.MIPStarRE.LDT.Pasting.gHatRotatedHalfProductOutcomeOperator, _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator, hhead]
  | succ i =>
      intro xs gs
      let xsPrefix : _root_.LIDT.MIPStarRE.LDT.PointTuple params (i + 1) := fun j => xs ⟨j.1, by omega⟩
      let gsPrefix : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params (i + 1) := fun j => gs ⟨j.1, by omega⟩
      have htail :
          _root_.LIDT.MIPStarRE.LDT.Pasting.pointTupleTail ((_root_.LIDT.MIPStarRE.LDT.Pasting.pointTupleLastReverseEquiv params (i + 1)) xs) =
            (_root_.LIDT.MIPStarRE.LDT.Pasting.pointTupleLastReverseEquiv params i) xsPrefix := by
        funext j
        cases j using Fin.cases with
        | zero =>
            simp [_root_.LIDT.MIPStarRE.LDT.Pasting.pointTupleTail, _root_.LIDT.MIPStarRE.LDT.Pasting.pointTupleLastReverseEquiv, xsPrefix]
        | succ j =>
            simpa only [_root_.LIDT.MIPStarRE.LDT.Pasting.pointTupleTail, _root_.LIDT.MIPStarRE.LDT.Pasting.pointTupleLastReverseEquiv, Equiv.coe_fn_mk,
              Fin.cons_succ, xsPrefix] using
              congrArg xs (Fin.ext (by
                change i - ((j : ℕ) + 1) = i - 1 - (j : ℕ)
                omega))
      have hgtail :
          _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleOutcomeTail ((_root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleOutcomeLastReverseEquiv params (i + 1)) gs) =
            (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleOutcomeLastReverseEquiv params i) gsPrefix := by
        funext j
        cases j using Fin.cases with
        | zero =>
            simp [_root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleOutcomeTail, _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleOutcomeLastReverseEquiv, gsPrefix]
        | succ j =>
            simpa only [_root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleOutcomeTail, _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleOutcomeLastReverseEquiv,
              Equiv.coe_fn_mk, Fin.cons_succ, gsPrefix] using
              congrArg gs (Fin.ext (by
                change i - ((j : ℕ) + 1) = i - 1 - (j : ℕ)
                omega))
      have hprefixAdj :=
        _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProduct_lastReverse_eq_conjTranspose params family i xsPrefix gsPrefix
      have hhead :
          ((_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family (xs ⟨i + 1, by omega⟩)).outcome
              (gs ⟨i + 1, by omega⟩))ᴴ =
            (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family (xs ⟨i + 1, by omega⟩)).outcome
              (gs ⟨i + 1, by omega⟩) := by
        exact (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family (xs ⟨i + 1, by omega⟩)).outcome_hermitian
          (gs ⟨i + 1, by omega⟩)
      have hfront :
          _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family (i + 1 + 1)
              ((_root_.LIDT.MIPStarRE.LDT.Pasting.pointTupleLastFrontEquiv params (i + 1)) xs)
              ((_root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleOutcomeLastFrontEquiv params (i + 1)) gs) =
            (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family (xs ⟨i + 1, by omega⟩)).outcome
                (gs ⟨i + 1, by omega⟩) *
              _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family (i + 1) xsPrefix gsPrefix := by
        have hfrontTail :
            _root_.LIDT.MIPStarRE.LDT.Pasting.pointTupleTail ((_root_.LIDT.MIPStarRE.LDT.Pasting.pointTupleLastFrontEquiv params (i + 1)) xs) =
              xsPrefix := by
          funext j
          simp [_root_.LIDT.MIPStarRE.LDT.Pasting.pointTupleTail, _root_.LIDT.MIPStarRE.LDT.Pasting.pointTupleLastFrontEquiv, xsPrefix]
        have hfrontGTail :
            _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleOutcomeTail ((_root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleOutcomeLastFrontEquiv params (i + 1)) gs) =
              gsPrefix := by
          funext j
          simp [_root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleOutcomeTail, _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleOutcomeLastFrontEquiv, gsPrefix]
        rw [_root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator]
        rw [hfrontTail, hfrontGTail]
        simp [_root_.LIDT.MIPStarRE.LDT.Pasting.pointTupleLastFrontEquiv, _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleOutcomeLastFrontEquiv]
      rw [_root_.LIDT.MIPStarRE.LDT.Pasting.gHatRotatedHalfProductOutcomeOperator]
      rw [htail, hgtail]
      rw [hprefixAdj]
      rw [hfront, Matrix.conjTranspose_mul, hhead]
      rfl
