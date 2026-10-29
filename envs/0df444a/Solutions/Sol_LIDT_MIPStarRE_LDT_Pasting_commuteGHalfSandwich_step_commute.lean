-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_step_commute
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T16:17:05.541605+00:00
-- url     : https://prove2.me/submissions/64b3a289-620a-4b58-9128-1d88de790b49

-- Generated proof for MIPStarRE.LDT.Pasting.commuteGHalfSandwich_step_commute.
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
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.RingTheory.MvPolynomial.Basic
import Theorems.Thm_LIDT_MIPStarRE_LDT_CommutativityPoints_sddOpRel_congr_outcome
import Theorems.Thm_LIDT_MIPStarRE_LDT_CommutativityPoints_sddOpRel_reindex
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_gHatPairProduct_sddOpRel_triple
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_gHatReverseHalfProduct_sum_adjoint_mul_le_one

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
# Section 12 pasting: commute G half-sandwich move lemmas

This module contains the move-chain lemmas for the half-sandwich commutation
chain.  The split reindexing lemmas and the two-term base case are kept in
`StepLemmas.Split`.

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
    (ψbi : _root_.LIDT.MIPStarRE.LDT.QuantumState (ι × ι))
    (family : _root_.LIDT.MIPStarRE.LDT.IdxPolyFamily params ι)
    (gamma zeta : _root_.LIDT.MIPStarRE.LDT.Error) (r : ℕ)
    (hcom : _root_.LIDT.MIPStarRE.LDT.SDDOpRel ψbi
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SlicePairQuestion params))
      (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatPairProductLeft params family)
      (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatPairProductRight params family)
      (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatCommutationError params gamma zeta)) :
    _root_.LIDT.MIPStarRE.LDT.SDDOpRel ψbi
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params × _root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params × _root_.LIDT.MIPStarRE.LDT.PointTuple params r))
      (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_moveFamily params family r)
      (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_commuteFamily params family r)
      (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatCommutationError params gamma zeta) := by
  let C : (_root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params × _root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params × _root_.LIDT.MIPStarRE.LDT.PointTuple params r) →
      (_root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params) → _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params r →
      _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι) :=
    fun q _ gt => _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι)
      (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatReverseHalfProductOutcomeOperator params family r q.2.2 gt)
  have hC :
      ∀ q a,
        ∑ gt : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params r, (C q a gt)ᴴ * C q a gt ≤ 1 := by
    intro q a
    calc
      ∑ gt : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params r, (C q a gt)ᴴ * C q a gt
        = ∑ gt : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params r,
            _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι)
              (((_root_.LIDT.MIPStarRE.LDT.Pasting.gHatReverseHalfProductOutcomeOperator params family r q.2.2 gt)ᴴ) *
                _root_.LIDT.MIPStarRE.LDT.Pasting.gHatReverseHalfProductOutcomeOperator params family r q.2.2 gt) := by
                  refine Finset.sum_congr rfl ?_
                  intro gt _
                  rw [show (_root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι)
                      (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatReverseHalfProductOutcomeOperator params family r q.2.2 gt))ᴴ =
                      _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι)
                        ((_root_.LIDT.MIPStarRE.LDT.Pasting.gHatReverseHalfProductOutcomeOperator params family r q.2.2 gt)ᴴ) by
                    simpa [_root_.LIDT.MIPStarRE.LDT.rightTensor, _root_.LIDT.MIPStarRE.LDT.opTensor] using
                      (_root_.LIDT.MIPStarRE.LDT.conjTranspose_opTensor (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι)
                        (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatReverseHalfProductOutcomeOperator params family r q.2.2 gt))]
                  simp [C, _root_.LIDT.MIPStarRE.LDT.rightTensor_mul_rightTensor]
      _ = _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι)
            (∑ gt : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params r,
              ((_root_.LIDT.MIPStarRE.LDT.Pasting.gHatReverseHalfProductOutcomeOperator params family r q.2.2 gt)ᴴ) *
                _root_.LIDT.MIPStarRE.LDT.Pasting.gHatReverseHalfProductOutcomeOperator params family r q.2.2 gt) := by
                  simpa using (_root_.LIDT.MIPStarRE.LDT.rightTensor_finset_sum (ι₁ := ι) Finset.univ
                    (fun gt => ((_root_.LIDT.MIPStarRE.LDT.Pasting.gHatReverseHalfProductOutcomeOperator params family r q.2.2 gt)ᴴ) *
                      _root_.LIDT.MIPStarRE.LDT.Pasting.gHatReverseHalfProductOutcomeOperator params family r q.2.2 gt))
      _ ≤ 1 := by
            exact _root_.LIDT.MIPStarRE.LDT.rightTensor_le_one (ι₁ := ι)
              (A := ∑ gt : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params r,
                ((_root_.LIDT.MIPStarRE.LDT.Pasting.gHatReverseHalfProductOutcomeOperator params family r q.2.2 gt)ᴴ) *
                  _root_.LIDT.MIPStarRE.LDT.Pasting.gHatReverseHalfProductOutcomeOperator params family r q.2.2 gt)
              (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatReverseHalfProduct_sum_adjoint_mul_le_one params family r q.2.2)
  let rawSource : _root_.LIDT.MIPStarRE.LDT.IdxOpFamily (_root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params × _root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params × _root_.LIDT.MIPStarRE.LDT.PointTuple params r)
      ((_root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params) × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params r) (ι × ι) :=
    fun q =>
      { outcome := fun ag : (_root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params) × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params r =>
          C q ag.1 ag.2 * (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatPairProductLeft params family (q.1, q.2.1)).outcome ag.1
        total := ∑ ag : (_root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params) × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params r,
          C q ag.1 ag.2 * (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatPairProductLeft params family (q.1, q.2.1)).outcome ag.1 }
  let rawTarget : _root_.LIDT.MIPStarRE.LDT.IdxOpFamily (_root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params × _root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params × _root_.LIDT.MIPStarRE.LDT.PointTuple params r)
      ((_root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params) × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params r) (ι × ι) :=
    fun q =>
      { outcome := fun ag : (_root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params) × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params r =>
          C q ag.1 ag.2 * (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatPairProductRight params family (q.1, q.2.1)).outcome ag.1
        total := ∑ ag : (_root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params) × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params r,
          C q ag.1 ag.2 * (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatPairProductRight params family (q.1, q.2.1)).outcome ag.1 }
  have hcab :=
    _root_.LIDT.MIPStarRE.LDT.Preliminaries.cabApproxDelta_raw ψbi
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params × _root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params × _root_.LIDT.MIPStarRE.LDT.PointTuple params r))
      (fun q => _root_.LIDT.MIPStarRE.LDT.Pasting.gHatPairProductLeft params family (q.1, q.2.1))
      (fun q => _root_.LIDT.MIPStarRE.LDT.Pasting.gHatPairProductRight params family (q.1, q.2.1))
      C (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatCommutationError params gamma zeta)
      (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatPairProduct_sddOpRel_triple params ψbi family gamma zeta r hcom)
      hC
  have hreindex := _root_.LIDT.MIPStarRE.LDT.CommutativityPoints.sddOpRel_reindex (_root_.LIDT.MIPStarRE.LDT.Pasting.pairTailOutcomeEquiv params r)
    ψbi
    (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params × _root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params × _root_.LIDT.MIPStarRE.LDT.PointTuple params r))
    rawSource rawTarget (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatCommutationError params gamma zeta) hcab
  let reindexedSource :
      _root_.LIDT.MIPStarRE.LDT.IdxOpFamily (_root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params × _root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params × _root_.LIDT.MIPStarRE.LDT.PointTuple params r)
      (_root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params r) (ι × ι) :=
    fun q =>
      { outcome := fun a' => (rawSource q).outcome ((_root_.LIDT.MIPStarRE.LDT.Pasting.pairTailOutcomeEquiv params r).symm a')
        total := (rawSource q).total }
  let reindexedTarget :
      _root_.LIDT.MIPStarRE.LDT.IdxOpFamily (_root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params × _root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params × _root_.LIDT.MIPStarRE.LDT.PointTuple params r)
      (_root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params r) (ι × ι) :=
    fun q =>
      { outcome := fun a' => (rawTarget q).outcome ((_root_.LIDT.MIPStarRE.LDT.Pasting.pairTailOutcomeEquiv params r).symm a')
        total := (rawTarget q).total }
  exact _root_.LIDT.MIPStarRE.LDT.CommutativityPoints.sddOpRel_congr_outcome ψbi
    (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params × _root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params × _root_.LIDT.MIPStarRE.LDT.PointTuple params r))
    reindexedSource reindexedTarget
    (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_moveFamily params family r)
    (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_commuteFamily params family r)
    (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatCommutationError params gamma zeta)
    (fun q ogs => by
      let A := (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome ogs.1
      let B := (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.2.1).outcome ogs.2.1
      let T := _root_.LIDT.MIPStarRE.LDT.Pasting.gHatReverseHalfProductOutcomeOperator params family r q.2.2 ogs.2.2
      calc
        (reindexedSource q).outcome ogs
          = _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) T * _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A * B) := by
              simp [reindexedSource, rawSource, _root_.LIDT.MIPStarRE.LDT.Pasting.pairTailOutcomeEquiv, C,
                _root_.LIDT.MIPStarRE.LDT.Pasting.gHatPairProductLeft, _root_.LIDT.MIPStarRE.LDT.CommutativityPoints.orderedProductOpFamily, _root_.LIDT.MIPStarRE.LDT.OpFamily.leftPlacedOpFamily,
                A, B, T]
        _ = _root_.LIDT.MIPStarRE.LDT.opTensor (A * B) T := by
              rw [_root_.LIDT.MIPStarRE.LDT.rightTensor_mul_leftTensor_eq_opTensor]
        _ = _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A * B) * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) T := by
              rw [_root_.LIDT.MIPStarRE.LDT.leftTensor_mul_rightTensor_eq_opTensor]
        _ = _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) A * _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) B * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) T := by
              rw [_root_.LIDT.MIPStarRE.LDT.leftTensor_mul_leftTensor]
        _ = (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_moveFamily params family r q).outcome ogs := by
              simp [_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_moveFamily, A, B, T, mul_assoc]
    )
    (fun q ogs => by
      let A := (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome ogs.1
      let B := (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.2.1).outcome ogs.2.1
      let T := _root_.LIDT.MIPStarRE.LDT.Pasting.gHatReverseHalfProductOutcomeOperator params family r q.2.2 ogs.2.2
      calc
        (reindexedTarget q).outcome ogs
          = _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) T * _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (B * A) := by
              simp [reindexedTarget, rawTarget, _root_.LIDT.MIPStarRE.LDT.Pasting.pairTailOutcomeEquiv, C,
                _root_.LIDT.MIPStarRE.LDT.Pasting.gHatPairProductRight, _root_.LIDT.MIPStarRE.LDT.CommutativityPoints.reversedProductOpFamily, _root_.LIDT.MIPStarRE.LDT.OpFamily.leftPlacedOpFamily,
                A, B, T]
        _ = _root_.LIDT.MIPStarRE.LDT.opTensor (B * A) T := by
              rw [_root_.LIDT.MIPStarRE.LDT.rightTensor_mul_leftTensor_eq_opTensor]
        _ = _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (B * A) * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) T := by
              rw [_root_.LIDT.MIPStarRE.LDT.leftTensor_mul_rightTensor_eq_opTensor]
        _ = _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) B * _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) A * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) T := by
              rw [_root_.LIDT.MIPStarRE.LDT.leftTensor_mul_leftTensor]
        _ = (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_commuteFamily params family r q).outcome ogs := by
              simp [_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_commuteFamily, A, B, T, mul_assoc]
    )
    hreindex
