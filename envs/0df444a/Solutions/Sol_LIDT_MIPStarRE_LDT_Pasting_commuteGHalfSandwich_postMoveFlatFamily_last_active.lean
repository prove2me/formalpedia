-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatFamily_last_active
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T16:05:43.03519+00:00
-- url     : https://prove2.me/submissions/9dc15d9a-7c76-4b7f-8020-d36d53978b35

-- Generated proof for MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatFamily_last_active.
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
















lemma commuteGHalfSandwich_postMoveFlatLength_eq
    (r : ℕ) :
    commuteGHalfSandwich_postMoveFlatLength r = 2 * r + 1 := by
  induction r with
  | zero => rfl
  | succ r ih =>
      simp [commuteGHalfSandwich_postMoveFlatLength, ih, Nat.mul_add,
        Nat.add_left_comm, Nat.add_comm]

lemma commuteGHalfSandwich_secondSliceLift_recursiveTarget
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ)
    (q : MoveQ params (r + 1))
    (ogs : MoveO params (r + 1)) :
    (commuteGHalfSandwich_secondSliceLiftFamily params family r
      (commuteGHalfSandwich_recursiveTargetFamily params family r) q).outcome
        ogs =
      (commuteGHalfSandwich_recursiveTargetFamily params family (r + 1) q).outcome ogs := by
  simp [commuteGHalfSandwich_secondSliceLiftFamily,
    commuteGHalfSandwich_recursiveTargetFamily, headTailRotatedFamily,
    gHatHalfProductOutcomeOperator,
    leftTensor_mul_leftTensor, mul_assoc]















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

open LIDT.MIPStarRE.LDT.Pasting

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

theorem solution
    (params : _root_.LIDT.MIPStarRE.LDT.Parameters) [_root_.LIDT.MIPStarRE.LDT.FieldModel params.q]
    (family : _root_.LIDT.MIPStarRE.LDT.IdxPolyFamily params ι) :
    ∀ r q ogs,
      (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatFamily params family r
          (Fin.last (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatLength r)) q).outcome
            ogs =
        (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_recursiveTargetFamily params family r q).outcome ogs
  | 0, q, ogs => by
      simp [_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatFamily, _root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatLength,
        _root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_recursiveTargetFamily, _root_.LIDT.MIPStarRE.LDT.Pasting.headTailRotatedFamily,
        _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator,
        _root_.LIDT.MIPStarRE.LDT.leftTensor_mul_leftTensor]
  | r + 1, q, ogs => by
      let q' : _root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params × _root_.LIDT.MIPStarRE.LDT.PointTuple params (r + 1) := (q.1, q.2.2)
      let ogs' : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params (r + 1) := (ogs.1, ogs.2.2)
      let q'' : _root_.LIDT.MIPStarRE.LDT.Pasting.MoveQ params r :=
        (_root_.LIDT.MIPStarRE.LDT.Pasting.splitSuccQuestionEquiv params r) q'
      let ogs'' : _root_.LIDT.MIPStarRE.LDT.Pasting.MoveO params r :=
        (_root_.LIDT.MIPStarRE.LDT.Pasting.splitSuccOutcomeEquiv params r) ogs'
      have hsmall :
          (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatFamily params family r
              (Fin.last (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatLength r)) q'').outcome ogs'' =
            (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_recursiveTargetFamily params family r
              q'').outcome ogs'' := by
        simpa using solution params family r
          q'' ogs''
      have hsmall' :
          (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatFamily params family r
              ⟨2 * (r + 1) - 1, by
                rw [_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatLength_eq]
                omega⟩ q'').outcome ogs'' =
            (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_recursiveTargetFamily params family r q'').outcome ogs'' := by
        have hlast_idx :
            (⟨2 * (r + 1) - 1, by
                have hlt : 2 * (r + 1) - 1 < _root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatLength r + 1 := by
                  rw [_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatLength_eq]
                  omega
                exact hlt⟩ : Fin (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatLength r + 1)) =
              Fin.last (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatLength r) := by
          ext
          simp [Fin.last, _root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatLength_eq, Nat.mul_add,
             Nat.add_comm]
        simpa [hlast_idx] using hsmall
      calc
        (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatFamily params family (r + 1)
            (Fin.last (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatLength (r + 1))) q).outcome ogs
          = (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_prefixSecondSliceLeftFamily params family (r + 1)
              (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_splitSuccLiftFamily params r
                (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatFamily params family r
                  ⟨2 * (r + 1) - 1, by
                    have hlt :
                        2 * (r + 1) - 1 < _root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatLength r + 1 := by
                      rw [_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatLength_eq]
                      omega
                    exact hlt⟩)) q).outcome ogs := by
                have hlength_ne : _root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatLength (r + 1) ≠ 1 := by
                  rw [_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatLength_eq]
                  omega
                have hindex :
                    (⟨2 * r + 1, by
                        rw [_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatLength_eq]
                        omega⟩ : Fin (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatLength r + 1)) =
                      ⟨2 * (r + 1) - 1, by
                        rw [_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatLength_eq]
                        omega⟩ := by
                  apply Fin.ext
                  dsimp
                  omega
                simp [_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatFamily,
                  _root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatLength_eq, hlength_ne, hindex]
        _ = (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_prefixSecondSliceLeftFamily params family (r + 1)
              (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_splitSuccLiftFamily params r
                (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_recursiveTargetFamily params family r)) q).outcome ogs := by
                change
                  _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                      ((_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.2.1).outcome ogs.2.1) *
                    ((_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatFamily params family r
                        ⟨2 * (r + 1) - 1, by
                          have hlt :
                              2 * (r + 1) - 1 < _root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatLength r + 1 := by
                            rw [_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_postMoveFlatLength_eq]
                            omega
                          exact hlt⟩ q'').outcome ogs'') =
                    _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                        ((_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.2.1).outcome ogs.2.1) *
                      ((_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_recursiveTargetFamily params family r q'').outcome
                        ogs'')
                exact congrArg
                  (fun X =>
                    let G := (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.2.1).outcome ogs.2.1
                    _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) G * X)
                  hsmall'
        _ = (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_recursiveTargetFamily params family (r + 1) q).outcome ogs := by
              exact (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_prefixSecondSliceLeft_splitSuccLift_eq_secondSliceLift
                  params family r
                (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_recursiveTargetFamily params family r) q ogs).trans
                  (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_secondSliceLift_recursiveTarget params family r q ogs)
