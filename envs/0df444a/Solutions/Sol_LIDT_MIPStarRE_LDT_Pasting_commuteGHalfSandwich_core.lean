-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_core
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T17:30:45.832019+00:00
-- url     : https://prove2.me/submissions/172e2b4f-6f5d-4988-b03d-0e34f6b2dba9

-- Generated proof for MIPStarRE.LDT.Pasting.commuteGHalfSandwich_core.
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
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_commuteGHalfSandwich_core_two
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_commuteGHalfSandwich_error_bound
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_commuteGHalfSandwich_flatChainError_sum
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_commuteGHalfSandwich_flatChainFamily_last
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_commuteGHalfSandwich_flatChainStep
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_commuteGHalfSandwich_split_iff
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_commuteGHalfSandwich_split_succ_iff

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

/- Source helpers from MIPStarRE/LDT/Pasting/ComparisonLemmas/CommuteGHalfSandwich/MoveChain/Chain.lean. -/
/-!
# Section 12 pasting: half-sandwich move chain

This module defines the recursive sequence of operator families which moves a
completed-slice factor through the half-product.  The adjacent edges in this
sequence are supplied by the self-consistency estimate for the completed-slice
family.

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


/-! ## Move chain: recursive family, step lemma, and aggregate

The recursive `moveChainFamily` indexed over `Fin (r+1)`, with the step lemma
`moveChain_step` and the aggregate lemma `move_chain` that composes the
`r` self-consistency edges.
-/


lemma commuteGHalfSandwich_moveChainFamily_zero
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    ∀ r q ogs,
      (commuteGHalfSandwich_moveChainFamily params family r 0 q).outcome
        ogs =
        (commuteGHalfSandwich_moveSourceFamily params family r q).outcome ogs
  | 0, q, ogs => by rfl
  | r + 1, q, ogs => by
      simp [commuteGHalfSandwich_moveChainFamily, commuteGHalfSandwich_moveChainLiftFamily,
        commuteGHalfSandwich_moveSourceFamily,
        commuteGHalfSandwich_moveChainFamily_zero params family r,
        gHatHalfProductOutcomeOperator, leftTensor_mul_leftTensor, mul_assoc]





end MIPStarRE.LDT.Pasting

end

/- Source helpers from MIPStarRE/LDT/Preliminaries/DistanceBounds.lean. -/
/-!
# Preliminary comparison theorems: distance bounds

Triangle-inequality style bounds for `SDDRel` and `SDDOpRel`.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT

/-! ### Infrastructure: triangle inequality for `SDDRel` -/















/-! ### Infrastructure: triangle inequality for `SDDOpRel` -/

/-- The operator-family squared-distance defect is nonnegative. -/
theorem qSDDOp_nonneg
    {Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι] [Fintype Outcome]
    (ψ : QuantumState ι) (A B : OpFamily Outcome ι) :
    0 ≤ qSDDOp ψ A B := by
  unfold qSDDOp qSDDCore
  exact Finset.sum_nonneg fun a _ => ev_adjoint_self_nonneg ψ _












end MIPStarRE.LDT.Preliminaries

end

/- Source helpers from MIPStarRE/LDT/Pasting/ComparisonLemmas/CommuteGHalfSandwich/MoveChain/FlatChain.lean. -/
/-!
# Section 12 pasting: half-sandwich flat chain

This module defines the post-move and combined flat chains used after the
distinguished completed-slice factor has been moved to the right tensor
register.  The chain alternates between pairwise commutation and
self-consistency steps, with an explicit error sequence for the final
composition.

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


/-! ## Post-move flat chain and flat-chain definitions

The post-move flat chain (`postMoveFlatFamily`, `postMoveFlatError`) and the
combined flat chain (`flatChainFamily`, `flatChainError`) together with their
endpoint and summation lemmas.
-/
















lemma commuteGHalfSandwich_postMoveFlatLength_eq
    (r : ℕ) :
    commuteGHalfSandwich_postMoveFlatLength r = 2 * r + 1 := by
  induction r with
  | zero => rfl
  | succ r ih =>
      simp [commuteGHalfSandwich_postMoveFlatLength, ih, Nat.mul_add,
        Nat.add_left_comm, Nat.add_comm]









lemma commuteGHalfSandwich_flatChainFamily_zero
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (r : ℕ) (q : MoveQ params r)
    (ogs : MoveO params r) :
    (commuteGHalfSandwich_flatChainFamily params family r 0 q).outcome
      ogs =
      (commuteGHalfSandwich_moveSourceFamily params family r q).outcome ogs := by
  simp [commuteGHalfSandwich_flatChainFamily,
    commuteGHalfSandwich_moveChainFamily_zero params family r]







end MIPStarRE.LDT.Pasting

end

end LIDT

open LIDT
/-!
# Section 12 pasting: half-sandwich chain assembly

This module assembles the move chain, the flat post-move chain, and the
move-back chain to prove the operator-family estimate used by
`lem:commute-g-half-sandwich`.

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


/-! ## Main theorem: `commuteGHalfSandwich_core`

The flat-chain construction and the final error envelope.
-/

theorem solution
    (params : _root_.LIDT.MIPStarRE.LDT.Parameters)
    [_root_.LIDT.MIPStarRE.LDT.FieldModel params.q]
    (ψbi : _root_.LIDT.MIPStarRE.LDT.QuantumState (ι × ι))
    (family : _root_.LIDT.MIPStarRE.LDT.IdxPolyFamily params ι)
    (gamma zeta : _root_.LIDT.MIPStarRE.LDT.Error) (k : ℕ) (hk : 2 ≤ k)
    (hzeta_le : zeta ≤ 1)
    (hsc : _root_.LIDT.MIPStarRE.LDT.SDDRel ψbi
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params))
      (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatSelfConsistencyLeftFamily params family)
      (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatSelfConsistencyRightFamily params family)
      (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatSelfConsistencyError zeta))
    (hcom : _root_.LIDT.MIPStarRE.LDT.SDDOpRel ψbi
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SlicePairQuestion params))
      (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatPairProductLeft params family)
      (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatPairProductRight params family)
      (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatCommutationError params gamma zeta)) :
    _root_.LIDT.MIPStarRE.LDT.SDDOpRel ψbi
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.PointTuple params k))
      (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfSandwichLeft params family k)
      (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfSandwichRight params family k)
      (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwichError params gamma zeta k) := by
  by_cases hk2 : k = 2
  · subst hk2
    exact _root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_core_two params ψbi family gamma zeta hcom
  · have hk3 : 3 ≤ k := by omega
    let r : ℕ := k - 2
    have hk_eq : k = r + 2 := by
      dsimp [r]
      omega
    have hsc0 := hsc
    have hcom0 := hcom
    rcases hsc with ⟨hν2⟩
    have hν2_nonneg : 0 ≤ _root_.LIDT.MIPStarRE.LDT.Pasting.gHatSelfConsistencyError zeta := by
      exact le_trans
        (_root_.LIDT.MIPStarRE.LDT.avgOver_nonneg (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params))
          (fun q => _root_.LIDT.MIPStarRE.LDT.qSDD ψbi (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatSelfConsistencyLeftFamily params family q)
            (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatSelfConsistencyRightFamily params family q))
          (fun q => _root_.LIDT.MIPStarRE.LDT.qSDD_nonneg ψbi _ _))
        hν2
    have hzeta_nonneg : 0 ≤ zeta := by
      simpa [_root_.LIDT.MIPStarRE.LDT.Pasting.gHatSelfConsistencyError] using hν2_nonneg
    rcases hcom with ⟨hν3⟩
    have hν3_nonneg : 0 ≤ _root_.LIDT.MIPStarRE.LDT.Pasting.gHatCommutationError params gamma zeta := by
      exact le_trans
        (_root_.LIDT.MIPStarRE.LDT.avgOver_nonneg (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SlicePairQuestion params))
          (fun q => _root_.LIDT.MIPStarRE.LDT.qSDDOp ψbi (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatPairProductLeft params family q)
            (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatPairProductRight params family q))
          (fun q => _root_.LIDT.MIPStarRE.LDT.Preliminaries.qSDDOp_nonneg ψbi _ _))
        hν3
    have hchain := _root_.LIDT.MIPStarRE.LDT.Preliminaries.sddOpRel_chain
      ψbi
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.MoveQ params r))
      (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_flatChainLength r)
      (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_flatChainFamily params family r)
      (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_flatChainError params gamma zeta r)
      (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_flatChainStep params ψbi family gamma zeta hsc0 hcom0 r)
    have hsplit :
        _root_.LIDT.MIPStarRE.LDT.SDDOpRel ψbi
          (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.MoveQ params r))
          (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_moveSourceFamily params family r)
          (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_recursiveTargetFamily params family r)
          (((_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_flatChainLength r : _root_.LIDT.MIPStarRE.LDT.Error)) *
            ∑ i : Fin (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_flatChainLength r),
              _root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_flatChainError params gamma zeta r i) := by
      exact _root_.LIDT.MIPStarRE.LDT.CommutativityPoints.sddOpRel_congr_outcome ψbi
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.MoveQ params r))
        ((_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_flatChainFamily params family r) 0)
        ((_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_flatChainFamily params family r)
          (Fin.last (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_flatChainLength r)))
        (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_moveSourceFamily params family r)
        (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_recursiveTargetFamily params family r)
        (((_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_flatChainLength r : _root_.LIDT.MIPStarRE.LDT.Error)) *
          ∑ i : Fin (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_flatChainLength r),
            _root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_flatChainError params gamma zeta r i)
        (fun q ogs => by
          simpa using _root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_flatChainFamily_zero params family r q ogs)
        (fun q ogs => by
          simpa using _root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_flatChainFamily_last params family r q ogs)
        hchain
    have hsplitOrdered :
        _root_.LIDT.MIPStarRE.LDT.SDDOpRel ψbi
          (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params × _root_.LIDT.MIPStarRE.LDT.PointTuple params (r + 1)))
          (_root_.LIDT.MIPStarRE.LDT.Pasting.headTailOrderedFamily params family (r + 1))
          (_root_.LIDT.MIPStarRE.LDT.Pasting.headTailRotatedFamily params family (r + 1))
          (((_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_flatChainLength r : _root_.LIDT.MIPStarRE.LDT.Error)) *
            ∑ i : Fin (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_flatChainLength r),
              _root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_flatChainError params gamma zeta r i) :=
      (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_split_succ_iff params ψbi family r
        (((_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_flatChainLength r : _root_.LIDT.MIPStarRE.LDT.Error)) *
          ∑ i : Fin (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_flatChainLength r),
            _root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_flatChainError params gamma zeta r i)).2 hsplit
    have hpoint :
        _root_.LIDT.MIPStarRE.LDT.SDDOpRel ψbi
          (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.PointTuple params k))
          (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfSandwichLeft params family k)
          (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfSandwichRight params family k)
          (((_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_flatChainLength r : _root_.LIDT.MIPStarRE.LDT.Error)) *
            ∑ i : Fin (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_flatChainLength r),
              _root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_flatChainError params gamma zeta r i) := by
      rw [hk_eq]
      exact (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_split_iff params ψbi family (r + 1)
        (((_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_flatChainLength r : _root_.LIDT.MIPStarRE.LDT.Error)) *
          ∑ i : Fin (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_flatChainLength r),
            _root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_flatChainError params gamma zeta r i)).2 hsplitOrdered
    have hkR : (k : _root_.LIDT.MIPStarRE.LDT.Error) = (r : _root_.LIDT.MIPStarRE.LDT.Error) + 2 := by
      exact_mod_cast hk_eq
    have hsum :
        ∑ i : Fin (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_flatChainLength r),
            _root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_flatChainError params gamma zeta r i =
          4 * (r : _root_.LIDT.MIPStarRE.LDT.Error) * zeta +
            ((r + 1 : ℕ) : _root_.LIDT.MIPStarRE.LDT.Error) * _root_.LIDT.MIPStarRE.LDT.Pasting.gHatCommutationError params gamma zeta :=
      _root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_flatChainError_sum params gamma zeta r
    have hlen_le :
        ((_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_flatChainLength r : ℕ) : _root_.LIDT.MIPStarRE.LDT.Error) ≤ 3 * (k : _root_.LIDT.MIPStarRE.LDT.Error) := by
      have hflat :
          ((_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_flatChainLength r : ℕ) : _root_.LIDT.MIPStarRE.LDT.Error) =
            3 * (r : _root_.LIDT.MIPStarRE.LDT.Error) + 1 := by
        rw [_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_flatChainLength, _root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatLength_eq]
        norm_num [Nat.cast_add, Nat.cast_mul, Nat.cast_one]
        ring
      rw [hflat, hkR]
      nlinarith
    have hsum_le :
        4 * (r : _root_.LIDT.MIPStarRE.LDT.Error) * zeta + ((r + 1 : ℕ) : _root_.LIDT.MIPStarRE.LDT.Error) * _root_.LIDT.MIPStarRE.LDT.Pasting.gHatCommutationError params gamma zeta
          ≤ 4 * (k : _root_.LIDT.MIPStarRE.LDT.Error) * zeta + (k : _root_.LIDT.MIPStarRE.LDT.Error) * _root_.LIDT.MIPStarRE.LDT.Pasting.gHatCommutationError params gamma zeta := by
      rw [hkR]
      have hζextra : 0 ≤ 8 * zeta := by nlinarith [hzeta_nonneg]
      have hνextra : 0 ≤ _root_.LIDT.MIPStarRE.LDT.Pasting.gHatCommutationError params gamma zeta := hν3_nonneg
      have hcast_r1 : (((r + 1 : ℕ) : _root_.LIDT.MIPStarRE.LDT.Error)) = (r : _root_.LIDT.MIPStarRE.LDT.Error) + 1 := by
        norm_num [Nat.cast_add, Nat.cast_one]
      have hrewrite :
          4 * ((r : _root_.LIDT.MIPStarRE.LDT.Error) + 2) * zeta + ((r : _root_.LIDT.MIPStarRE.LDT.Error) + 2)
              * _root_.LIDT.MIPStarRE.LDT.Pasting.gHatCommutationError params gamma zeta =
            4 * (r : _root_.LIDT.MIPStarRE.LDT.Error) * zeta + ((r + 1 : ℕ) : _root_.LIDT.MIPStarRE.LDT.Error)
                * _root_.LIDT.MIPStarRE.LDT.Pasting.gHatCommutationError params gamma zeta +
              (8 * zeta + _root_.LIDT.MIPStarRE.LDT.Pasting.gHatCommutationError params gamma zeta) := by
        rw [hcast_r1]
        ring
      nlinarith [hrewrite, hζextra, hνextra]
    have hsum_nonneg :
        0 ≤
          4 * (r : _root_.LIDT.MIPStarRE.LDT.Error) * zeta +
            ((r + 1 : ℕ) : _root_.LIDT.MIPStarRE.LDT.Error) * _root_.LIDT.MIPStarRE.LDT.Pasting.gHatCommutationError params gamma zeta := by
      nlinarith [hzeta_nonneg, hν3_nonneg]
    have hraw_bound :
        (((_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_flatChainLength r : _root_.LIDT.MIPStarRE.LDT.Error)) *
            ∑ i : Fin (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_flatChainLength r),
              _root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_flatChainError params gamma zeta r i)
          ≤ 3 * (k : _root_.LIDT.MIPStarRE.LDT.Error) *
              (4 * (k : _root_.LIDT.MIPStarRE.LDT.Error) * zeta + (k : _root_.LIDT.MIPStarRE.LDT.Error) * _root_.LIDT.MIPStarRE.LDT.Pasting.gHatCommutationError params gamma zeta) := by
      rw [hsum]
      gcongr
    exact _root_.LIDT.MIPStarRE.LDT.Preliminaries.sddOpRel_mono ψbi
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.PointTuple params k))
      (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfSandwichLeft params family k)
      (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfSandwichRight params family k)
      (((_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_flatChainLength r : _root_.LIDT.MIPStarRE.LDT.Error)) *
        ∑ i : Fin (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_flatChainLength r),
          _root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_flatChainError params gamma zeta r i)
      (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwichError params gamma zeta k)
      hpoint
      (le_trans hraw_bound
        (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_error_bound params gamma zeta k hzeta_nonneg hzeta_le))
