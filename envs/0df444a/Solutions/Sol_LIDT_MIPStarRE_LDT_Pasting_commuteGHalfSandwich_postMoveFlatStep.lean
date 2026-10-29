-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatStep
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T17:22:25.486653+00:00
-- url     : https://prove2.me/submissions/11b6c513-dfb0-4808-b0e7-a7b4f96ffc6f

-- Generated proof for MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatStep.
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
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_commuteGHalfSandwich_commute_to_moveBackChainFamily_zero
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_commuteGHalfSandwich_moveBackChainFamily_zero_eq_secondSliceLift_moveFamily
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_commuteGHalfSandwich_prefixSecondSliceLeftLift
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_commuteGHalfSandwich_splitSuccLift
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














lemma commuteGHalfSandwich_commuteFamily_zero_eq_recursiveTarget
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (q : SliceQuestion params × SliceQuestion params × PointTuple params 0)
    (ogs : GHatOutcome params × GHatOutcome params × GHatTupleOutcome params 0) :
    (commuteGHalfSandwich_commuteFamily params family 0 q).outcome
      ogs =
      (commuteGHalfSandwich_recursiveTargetFamily params family 0 q).outcome ogs := by
  simp [commuteGHalfSandwich_commuteFamily, commuteGHalfSandwich_recursiveTargetFamily,
    headTailRotatedFamily, gHatHalfProductOutcomeOperator, gHatReverseHalfProductOutcomeOperator,
    rightTensor_one,
    leftTensor_mul_leftTensor]





lemma commuteGHalfSandwich_postMoveFlatFamily_zero_active
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    ∀ r q ogs,
      (commuteGHalfSandwich_postMoveFlatFamily params family r 0 q).outcome
        ogs =
        (commuteGHalfSandwich_moveFamily params family r q).outcome ogs
  | 0, q, ogs => by
      simp [commuteGHalfSandwich_postMoveFlatFamily, commuteGHalfSandwich_moveFamily,
        leftTensor_mul_leftTensor]
  | r + 1, q, ogs => by
      simp [commuteGHalfSandwich_postMoveFlatFamily]













end MIPStarRE.LDT.Pasting

end

/- Source helpers from MIPStarRE/LDT/Pasting/ComparisonLemmas/CommuteGHalfSandwich/MoveChain/Lifting.lean. -/
/-!
# Section 12 pasting: half-sandwich lifting constructions

This module contains the reindexing equivalences and lifted operator families
which transport an `r`-step half-sandwich move comparison to the corresponding
`r+1`-step comparison.

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


/-! ## Lifting families for the half-sandwich chain

Lifting constructions: swapped-front equivalences, `splitSuccLiftFamily`,
`prefixSecondSliceLeftFamily`, `secondSliceLiftFamily`, and the
`moveChainLift` construction that lifts an `r`-step chain to `r+1`.
-/


















lemma commuteGHalfSandwich_prefixSecondSliceLeft_splitSuccLift_eq_secondSliceLift
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ)
    (F : IdxOpFamily
      (MoveQ params r)
      (MoveO params r)
      (ι × ι))
    (q : MoveQ params (r + 1))
    (ogs : MoveO params (r + 1)) :
    (commuteGHalfSandwich_prefixSecondSliceLeftFamily params family (r + 1)
      (commuteGHalfSandwich_splitSuccLiftFamily params r F) q).outcome
        ogs =
      (commuteGHalfSandwich_secondSliceLiftFamily params family r F q).outcome ogs := by
  simp [commuteGHalfSandwich_prefixSecondSliceLeftFamily,
    commuteGHalfSandwich_splitSuccLiftFamily,
    commuteGHalfSandwich_secondSliceLiftFamily,
    splitSuccQuestionEquiv, splitSuccOutcomeEquiv]

















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
    ∀ r (i : Fin (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatLength r)),
      _root_.LIDT.MIPStarRE.LDT.SDDOpRel ψbi
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.MoveQ params r))
        ((_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatFamily params family r) i.castSucc)
        ((_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatFamily params family r) i.succ)
        ((_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatError params gamma zeta r) i)
  | 0, i => by
      fin_cases i
      have hcomm0 := _root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_step_commute params ψbi family gamma zeta 0 hcom
      exact _root_.LIDT.MIPStarRE.LDT.CommutativityPoints.sddOpRel_congr_outcome ψbi
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params × _root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params × _root_.LIDT.MIPStarRE.LDT.PointTuple params 0))
        (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_moveFamily params family 0)
        (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_commuteFamily params family 0)
        (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_moveFamily params family 0)
        (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_recursiveTargetFamily params family 0)
        (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatCommutationError params gamma zeta)
        (fun _ _ => rfl)
        (fun q ogs => _root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_commuteFamily_zero_eq_recursiveTarget params family
            q ogs)
        hcomm0
  | r + 1, i => by
      by_cases hi0 : i.1 = 0
      · have hcomm1 := _root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_step_commute
            params ψbi family gamma zeta (r + 1) hcom
        have hsrc_eq :
            ∀ q ogs,
              ((_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatFamily params family (r + 1))
                  i.castSucc q).outcome
                ogs =
                (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_moveFamily params family (r + 1) q).outcome ogs := by
          intro q ogs
          simp [_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatFamily, hi0]
        have htgt_eq :
            ∀ q ogs,
              ((_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatFamily params family (r + 1))
                  i.succ q).outcome
                ogs =
                (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_commuteFamily params family (r + 1) q).outcome ogs := by
          intro q ogs
          simp [_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatFamily, hi0]
        simpa [_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatError, hi0] using
          (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.sddOpRel_congr_outcome ψbi
            (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params × _root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params ×
                _root_.LIDT.MIPStarRE.LDT.PointTuple params (r + 1)))
            (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_moveFamily params family (r + 1))
            (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_commuteFamily params family (r + 1))
            ((_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatFamily params family (r + 1)) i.castSucc)
            ((_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatFamily params family (r + 1)) i.succ)
            (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatCommutationError params gamma zeta)
            (fun q ogs => (hsrc_eq q ogs).symm)
            (fun q ogs => (htgt_eq q ogs).symm)
            hcomm1)
      · by_cases hi1 : i.1 = 1
        · have hzero := _root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_commute_to_moveBackChainFamily_zero params ψbi
            family zeta (r := r) hsc
          have hsrc_eq :
              ∀ q ogs,
                ((_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatFamily params family (r + 1))
                  i.castSucc q).outcome
                  ogs =
                  (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_commuteFamily params family (r + 1) q).outcome ogs := by
            intro q ogs
            simp [_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatFamily, hi1]
          have htgt_eq :
              ∀ q ogs,
                ((_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatFamily params family (r + 1))
                  i.succ q).outcome
                  ogs =
                  ((_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_moveBackChainFamily params family r) 0 q).outcome
                    ogs := by
            intro q ogs
            have hi2 : i.1 + 1 ≠ 0 := by omega
            have hi2' : i.1 + 1 ≠ 1 := by omega
            have hinner0_nat : i.1 - 1 = 0 := by omega
            have hinner0 :
                (⟨i.1 - 1, by
                    have hi_lt : i.1 < _root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatLength r + 2 := by
                      exact i.2
                    omega⟩ : Fin (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatLength r + 1)) = 0 := by
              apply Fin.ext
              simp [hinner0_nat]
            let q' : _root_.LIDT.MIPStarRE.LDT.Pasting.MoveQ params r :=
              (q.1, q.2.2 0, _root_.LIDT.MIPStarRE.LDT.Pasting.pointTupleTail q.2.2)
            let ogs' : _root_.LIDT.MIPStarRE.LDT.Pasting.MoveO params r :=
              (ogs.1, ogs.2.2 0, _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleOutcomeTail ogs.2.2)
            have hzero_active :
                ((_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatFamily params family r) 0 q').outcome ogs' =
                  (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_moveFamily params family r q').outcome ogs' :=
              _root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatFamily_zero_active params family r q' ogs'
            have hsecond_eq :
                (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_prefixSecondSliceLeftFamily params family (r + 1)
                  (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_splitSuccLiftFamily params r
                    ((_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatFamily params family r) 0)) q).outcome
                      ogs =
                  (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_secondSliceLiftFamily params family r
                    (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_moveFamily params family r) q).outcome ogs := by
              calc
                (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_prefixSecondSliceLeftFamily params family (r + 1)
                  (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_splitSuccLiftFamily params r
                    ((_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatFamily params family r) 0)) q).outcome ogs
                    = (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_secondSliceLiftFamily params family r
                        ((_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatFamily params family r) 0)
                          q).outcome ogs := by
                          rw [
                  _root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_prefixSecondSliceLeft_splitSuccLift_eq_secondSliceLift
                          ]
                _ = (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_secondSliceLiftFamily params family r
                      (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_moveFamily params family r)
                      q).outcome ogs := by
                    change _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                      ((_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.2.1).outcome ogs.2.1) *
                        (((_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatFamily params family r) 0
                          q').outcome ogs') = _
                    exact congrArg
                      (fun X =>
                        let G := (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.2.1).outcome ogs.2.1
                        _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) G * X)
                      hzero_active
            have hi_ne_zero : i ≠ 0 := by
              intro hi
              subst i
              exact hi0 rfl
            calc
              ((_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatFamily params family (r + 1))
                  i.succ q).outcome ogs
                = (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_prefixSecondSliceLeftFamily params family (r + 1)
                    (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_splitSuccLiftFamily params r
                      ((_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatFamily params family r) 0)) q).outcome
                    ogs := by
                        conv_lhs => simp [_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatFamily, hi2, hi2']
                        simp [hi_ne_zero, hinner0]
              _ = (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_secondSliceLiftFamily params family r
                    (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_moveFamily params family r) q).outcome ogs := hsecond_eq
              _ = ((_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_moveBackChainFamily params family r) 0 q).outcome
                    ogs := by
                    simpa using
                      (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_moveBackChainFamily_zero_eq_secondSliceLift_moveFamily
                        params family r q ogs).symm
          simpa [_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatError, hi0, hi1] using
            (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.sddOpRel_congr_outcome ψbi
              (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params × _root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params ×
                  _root_.LIDT.MIPStarRE.LDT.PointTuple params (r + 1)))
              (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_commuteFamily params family (r + 1))
              ((_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_moveBackChainFamily params family r) 0)
              ((_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatFamily params family (r + 1)) i.castSucc)
              ((_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatFamily params family (r + 1)) i.succ)
              (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatSelfConsistencyError zeta)
              (fun q ogs => (hsrc_eq q ogs).symm)
              (fun q ogs => (htgt_eq q ogs).symm)
              hzero)
        · let j : Fin (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatLength r) :=
            ⟨i.1 - 2, by
              have hi_lt : i.1 < _root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatLength r + 2 := by
                exact i.2
              omega⟩
          have hsmall := solution params ψbi family gamma zeta hsc
              hcom r j
          have hprefix := _root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_prefixSecondSliceLeftLift params ψbi family (r + 1)
            (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_splitSuccLiftFamily params r
              ((_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatFamily params family r) j.castSucc))
            (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_splitSuccLiftFamily params r
              ((_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatFamily params family r) j.succ))
            ((_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatError params gamma zeta r) j)
            (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_splitSuccLift params ψbi r
              ((_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatFamily params family r) j.castSucc)
              ((_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatFamily params family r) j.succ)
              ((_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatError params gamma zeta r) j)
              hsmall)
          have hsrc_eq :
              ∀ q ogs,
                ((_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatFamily params family (r + 1))
                  i.castSucc q).outcome
                  ogs =
                  (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_prefixSecondSliceLeftFamily params family (r + 1)
                    (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_splitSuccLiftFamily params r
                      ((_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatFamily params family r) j.castSucc))
                        q).outcome ogs := by
            intro q ogs
            have hsrc_not0 : i.1 ≠ 0 := hi0
            have hsrc_not1 : i.1 ≠ 1 := hi1
            simp [_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatFamily, hsrc_not0, hsrc_not1, j]
          have htgt_eq :
              ∀ q ogs,
                ((_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatFamily params family (r + 1))
                  i.succ q).outcome
                  ogs =
                  (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_prefixSecondSliceLeftFamily params family (r + 1)
                    (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_splitSuccLiftFamily params r
                      ((_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatFamily params family r) j.succ))
                        q).outcome ogs := by
            intro q ogs
            have htgt_not0 : i.1 + 1 ≠ 0 := by omega
            have htgt_not1 : i.1 + 1 ≠ 1 := by omega
            have hi_ne_zero : i ≠ 0 := by
              intro hi
              subst i
              exact hi0 rfl
            have hj_succ :
                (j.succ : Fin (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatLength r + 1)) =
                  ⟨i.1 - 1, by
                    have hi_lt : i.1 < _root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatLength r + 2 := by
                      exact i.2
                    omega⟩ := by
              apply Fin.ext
              dsimp [j]
              omega
            calc
              ((_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatFamily params family (r + 1))
                  i.succ q).outcome ogs
                = (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_prefixSecondSliceLeftFamily params family (r + 1)
                    (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_splitSuccLiftFamily params r
                      ((_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatFamily params family r)
                        ⟨i.1 - 1, by
                          have hi_lt : i.1 < _root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatLength r + 2 := by
                            exact i.2
                          omega⟩)) q).outcome ogs := by
                        conv_lhs => simp [_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatFamily, htgt_not0,
                            htgt_not1]
                        simp [hi_ne_zero]
              _ = (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_prefixSecondSliceLeftFamily params family (r + 1)
                    (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_splitSuccLiftFamily params r
                      ((_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatFamily params family r) j.succ))
                        q).outcome ogs := by
                        have hidx :
                            ((_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatFamily params family r)
                              ⟨i.1 - 1, by
                                have hi_lt :
                                    i.1 < _root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatLength r + 2 := by
                                  exact i.2
                                omega⟩) =
                              ((_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatFamily params family r)
                                j.succ) := by
                                exact congrArg
                                  (fun idx =>
                                    (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatFamily params family r) idx)
                                  hj_succ.symm
                        simp [hidx]
          simpa [_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatError, hi0, hi1, j] using
            (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.sddOpRel_congr_outcome ψbi
              (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params × _root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params ×
                  _root_.LIDT.MIPStarRE.LDT.PointTuple params (r + 1)))
              (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_prefixSecondSliceLeftFamily params family (r + 1)
                (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_splitSuccLiftFamily params r
                  ((_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatFamily params family r) j.castSucc)))
              (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_prefixSecondSliceLeftFamily params family (r + 1)
                (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_splitSuccLiftFamily params r
                  ((_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatFamily params family r) j.succ)))
              ((_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatFamily params family (r + 1)) i.castSucc)
              ((_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatFamily params family (r + 1)) i.succ)
              ((_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatError params gamma zeta r) j)
              (fun q ogs => (hsrc_eq q ogs).symm)
              (fun q ogs => (htgt_eq q ogs).symm)
              hprefix)
