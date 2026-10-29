-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_flatChainStep
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T17:26:51.548105+00:00
-- url     : https://prove2.me/submissions/d7404470-6e17-439f-83bf-1cf4f6ddbb71

-- Generated proof for MIPStarRE.LDT.Pasting.commuteGHalfSandwich_flatChainStep.
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
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_commuteGHalfSandwich_moveChain_step
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_commuteGHalfSandwich_postMoveFlatStep
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_commuteGHalfSandwich_step_commute

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




lemma commuteGHalfSandwich_moveChainFamily_last
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    ∀ r q ogs,
      (commuteGHalfSandwich_moveChainFamily params family r (Fin.last r) q).outcome
        ogs =
        (commuteGHalfSandwich_moveFamily params family r q).outcome ogs
  | 0, q, ogs => by
      simp [commuteGHalfSandwich_moveChainFamily,
        commuteGHalfSandwich_moveSourceFamily, commuteGHalfSandwich_moveFamily,
        gHatHalfProductOutcomeOperator, gHatReverseHalfProductOutcomeOperator]
  | r + 1, q, ogs => by
      simp [commuteGHalfSandwich_moveChainFamily]



end MIPStarRE.LDT.Pasting

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





lemma commuteGHalfSandwich_postMoveFlatFamily_one_active
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ)
    (q : MoveQ params (r + 1))
    (ogs : MoveO params (r + 1)) :
    (commuteGHalfSandwich_postMoveFlatFamily params family (r + 1)
      ⟨1, by
        rw [commuteGHalfSandwich_postMoveFlatLength_eq]
        omega⟩ q).outcome
          ogs =
      (commuteGHalfSandwich_commuteFamily params family (r + 1) q).outcome ogs := by
  simp [commuteGHalfSandwich_postMoveFlatFamily]











end MIPStarRE.LDT.Pasting

end

end LIDT

open LIDT
/-!
# Section 12 pasting: half-sandwich flat-chain steps

This module proves the adjacent-edge estimates for the post-move and combined
flat chains.  These estimates are the local inputs to the final chain
composition in the proof of `commuteGHalfSandwich_core`.

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


/-! ## Flat-chain step lemmas

`postMoveFlatStep` builds the edges within the post-move phase, and
`flatChainStep` stitches the move-chain prefix and the post-move suffix
into one combined chain.
-/

theorem solution
    (params : _root_.LIDT.MIPStarRE.LDT.Parameters) [_root_.LIDT.MIPStarRE.LDT.FieldModel params.q]
    (ψbi : _root_.LIDT.MIPStarRE.LDT.QuantumState (ι × ι))
    (family : _root_.LIDT.MIPStarRE.LDT.IdxPolyFamily params ι)
    (gamma zeta : _root_.LIDT.MIPStarRE.LDT.Error)
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
    ∀ r (i : Fin (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_flatChainLength r)),
      _root_.LIDT.MIPStarRE.LDT.SDDOpRel ψbi
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.MoveQ params r))
        ((_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_flatChainFamily params family r) i.castSucc)
        ((_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_flatChainFamily params family r) i.succ)
        ((_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_flatChainError params gamma zeta r) i)
  | 0, i => by
      fin_cases i
      let izero : Fin (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatLength 0) :=
        ⟨0, by simp [_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatLength]⟩
      have hstep :=
        _root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatStep params ψbi family gamma zeta hsc hcom 0
          izero
      have htransport :
          _root_.LIDT.MIPStarRE.LDT.SDDOpRel ψbi (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.MoveQ params 0))
            (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_moveSourceFamily params family 0)
            (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_recursiveTargetFamily params family 0)
            (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatError params gamma zeta 0 izero) :=
        _root_.LIDT.MIPStarRE.LDT.CommutativityPoints.sddOpRel_congr_outcome ψbi
          (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.MoveQ params 0))
          (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_moveFamily params family 0)
          (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_recursiveTargetFamily params family 0)
          (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_moveSourceFamily params family 0)
          (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_recursiveTargetFamily params family 0)
          (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatError params gamma zeta 0 izero)
          (fun q ogs => by
            simp [_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_moveSourceFamily, _root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_moveFamily,
              _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator, _root_.LIDT.MIPStarRE.LDT.Pasting.gHatReverseHalfProductOutcomeOperator,
              _root_.LIDT.MIPStarRE.LDT.leftTensor_one, _root_.LIDT.MIPStarRE.LDT.leftTensor_mul_leftTensor, mul_assoc])
          (fun _ _ => rfl)
          hstep
      simpa [_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_flatChainFamily, _root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_flatChainError,
        _root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatLength, _root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatFamily,
        _root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_moveChainFamily, izero] using
        htransport
  | r + 1, i => by
      by_cases hi : i.1 < r + 1
      · let imove : Fin (r + 1) := ⟨i.1, hi⟩
        have hmove := _root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_moveChain_step params ψbi family zeta hsc (r + 1) imove
        have hsrc_eq :
            ∀ q ogs,
              ((_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_flatChainFamily params family (r + 1))
                  i.castSucc q).outcome
                ogs =
                ((_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_moveChainFamily params family (r + 1))
                  imove.castSucc q).outcome ogs := by
          intro q ogs
          have hsrc_le : i.1 ≤ r + 1 := by omega
          conv_lhs => simp [_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_flatChainFamily, hsrc_le]
          rfl
        have htgt_eq :
            ∀ q ogs,
              ((_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_flatChainFamily params family (r + 1))
                  i.succ q).outcome
                ogs =
                ((_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_moveChainFamily params family (r + 1))
                  imove.succ q).outcome ogs := by
          intro q ogs
          have htgt_le : i.1 ≤ r := by omega
          conv_lhs => simp [_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_flatChainFamily, htgt_le]
          rfl
        simpa [_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_flatChainError, hi] using
          (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.sddOpRel_congr_outcome ψbi
            (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params × _root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params ×
                _root_.LIDT.MIPStarRE.LDT.PointTuple params (r + 1)))
            ((_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_moveChainFamily params family (r + 1)) imove.castSucc)
            ((_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_moveChainFamily params family (r + 1)) imove.succ)
            ((_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_flatChainFamily params family (r + 1)) i.castSucc)
            ((_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_flatChainFamily params family (r + 1)) i.succ)
            (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatSelfConsistencyError zeta)
            (fun q ogs => (hsrc_eq q ogs).symm)
            (fun q ogs => (htgt_eq q ogs).symm)
            hmove)
      · have hge : r + 1 ≤ i.1 := by omega
        by_cases hboundary : i.1 = r + 1
        · have hcomm1 := _root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_step_commute
            params ψbi family gamma zeta (r + 1) hcom
          have hsrc_eq :
              ∀ q ogs,
                ((_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_flatChainFamily params family (r + 1))
                  i.castSucc q).outcome
                  ogs =
                  (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_moveFamily params family (r + 1) q).outcome ogs := by
            intro q ogs
            have hsrc_le : i.1 ≤ r + 1 := by omega
            conv_lhs => simp [_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_flatChainFamily, hsrc_le]
            simpa [hboundary, Fin.last] using
              _root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_moveChainFamily_last params family (r + 1) q ogs
          have htgt_eq :
              ∀ q ogs,
                ((_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_flatChainFamily params family (r + 1))
                  i.succ q).outcome
                  ogs =
                  (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_commuteFamily params family (r + 1) q).outcome ogs := by
            intro q ogs
            have htgt_not : ¬ i.1 ≤ r := by omega
            have hone_lt : 1 < _root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatLength (r + 1) + 1 := by
              rw [_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatLength_eq]
              omega
            calc
              ((_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_flatChainFamily params family (r + 1))
                  i.succ q).outcome ogs
                = (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatFamily params family (r + 1)
                    ⟨i.1 - r, by
                      simp [hboundary]⟩ q).outcome ogs := by
                        conv_lhs => simp [_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_flatChainFamily, htgt_not]
              _ = (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatFamily params family (r + 1)
                    ⟨1, by exact hone_lt⟩ q).outcome ogs := by
                    have hone :
                        (⟨i.1 - r, by simp [hboundary]⟩ :
                          Fin (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatLength (r + 1) + 1)) =
                          ⟨1, by exact hone_lt⟩ := by
                      apply Fin.ext
                      simp [hboundary]
                    exact congrArg
                      (fun idx => ((_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatFamily params family (r + 1))
                  idx q).outcome ogs)
                      hone
                  _ = (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_commuteFamily params family (r + 1) q).outcome
                    ogs := by
                    exact
                      _root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatFamily_one_active
                        params family (r := r) q ogs
          simpa [_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_flatChainError, hi, hboundary,
            _root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatError] using
            (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.sddOpRel_congr_outcome ψbi
              (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params × _root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params ×
                  _root_.LIDT.MIPStarRE.LDT.PointTuple params (r + 1)))
              (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_moveFamily params family (r + 1))
              (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_commuteFamily params family (r + 1))
              ((_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_flatChainFamily params family (r + 1)) i.castSucc)
              ((_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_flatChainFamily params family (r + 1)) i.succ)
              (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatCommutationError params gamma zeta)
              (fun q ogs => (hsrc_eq q ogs).symm)
              (fun q ogs => (htgt_eq q ogs).symm)
              hcomm1)
        · let j : Fin (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatLength (r + 1)) :=
            ⟨i.1 - (r + 1), by
              have hi_lt : i.1 < (r + 1) + _root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatLength (r + 1) := by
                exact i.2
              omega⟩
          have hsmall := _root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatStep params ψbi family gamma zeta hsc
              hcom (r + 1) j
          have hsrc_eq :
              ∀ q ogs,
                ((_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_flatChainFamily params family (r + 1))
                  i.castSucc q).outcome
                  ogs =
                  ((_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatFamily params family (r + 1))
                  j.castSucc q).outcome ogs := by
            intro q ogs
            have hsrc_not : ¬ i.1 ≤ r + 1 := by omega
            have hj_castSucc :
                (⟨i.1 - (r + 1), by
                    exact Nat.lt_trans j.2 (Nat.lt_succ_self _)⟩ :
                  Fin (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatLength (r + 1) + 1)) = j.castSucc := by
              apply Fin.ext
              simp [j]
            conv_lhs => simp [_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_flatChainFamily, hsrc_not]
            exact congrArg
              (fun idx => ((_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatFamily params family (r + 1))
                  idx q).outcome ogs)
              hj_castSucc
          have htgt_eq :
              ∀ q ogs,
                ((_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_flatChainFamily params family (r + 1))
                  i.succ q).outcome
                  ogs =
                  ((_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatFamily params family (r + 1))
                    j.succ q).outcome ogs := by
            intro q ogs
            have htgt_not : ¬ i.1 ≤ r := by omega
            have hge2 : r + 2 ≤ i.1 := by omega
            have hval : i.1 - r = (i.1 - (r + 1)) + 1 := by
              omega
            have hj_succ :
                (⟨i.1 - r, by
                    rw [hval]
                    simpa [j] using j.succ.is_lt⟩ :
                  Fin (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatLength (r + 1) + 1)) = j.succ := by
              apply Fin.ext
              simp [j, hval]
            conv_lhs => simp [_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_flatChainFamily, htgt_not]
            exact congrArg
              (fun idx => ((_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatFamily params family (r + 1))
                  idx q).outcome ogs)
              hj_succ
          simpa [_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_flatChainError, hi, hboundary, j] using
            (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.sddOpRel_congr_outcome ψbi
              (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params × _root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params ×
                  _root_.LIDT.MIPStarRE.LDT.PointTuple params (r + 1)))
              ((_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatFamily params family (r + 1)) j.castSucc)
              ((_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatFamily params family (r + 1)) j.succ)
              ((_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_flatChainFamily params family (r + 1)) i.castSucc)
              ((_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_flatChainFamily params family (r + 1)) i.succ)
              ((_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatError params gamma zeta (r + 1)) j)
              (fun q ogs => (hsrc_eq q ogs).symm)
              (fun q ogs => (htgt_eq q ogs).symm)
              hsmall)
