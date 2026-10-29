-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_moveChainLift_moveFamily_last
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T16:20:58.358147+00:00
-- url     : https://prove2.me/submissions/23329385-8f14-4c0b-8ed0-f4824e169bfa

-- Generated proof for MIPStarRE.LDT.Pasting.commuteGHalfSandwich_moveChainLift_moveFamily_last.
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
import Theorems.Thm_LIDT_MIPStarRE_LDT_CommutativityPoints_sddOpRel_reindex
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_commuteGHalfSandwich_moveStepMid_toTarget
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_sddOpRel_uniform_equiv

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




















lemma commuteGHalfSandwich_moveFamily_eq_moveStepTarget
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ)
    (q : MoveQ params (r + 1))
    (ogs : MoveO params (r + 1)) :
    (commuteGHalfSandwich_moveFamily params family (r + 1) q).outcome
      ogs =
      (commuteGHalfSandwich_moveStepTargetFamily params family r
        ((moveTailQuestionEquiv params r) q)).outcome
        ((moveTailOutcomeEquiv params r) ogs) := by
  let A := (gHatIdxMeas params family q.1).outcome ogs.1
  let B := (gHatIdxMeas params family q.2.1).outcome ogs.2.1
  let T := gHatReverseHalfProductOutcomeOperator params family r
    (pointTupleTail q.2.2) (gHatTupleOutcomeTail ogs.2.2)
  let G := (gHatIdxMeas params family (q.2.2 0)).outcome (ogs.2.2 0)
  calc
    (commuteGHalfSandwich_moveFamily params family (r + 1) q).outcome ogs
      = leftTensor (ι₂ := ι) A * leftTensor (ι₂ := ι) B *
          rightTensor (ι₁ := ι) (T * G) := by
          simp [commuteGHalfSandwich_moveFamily,
            A, B, T, G, gHatReverseHalfProductOutcomeOperator, leftTensor_mul_leftTensor]
    _ = leftTensor (ι₂ := ι) A * leftTensor (ι₂ := ι) B *
          (rightTensor (ι₁ := ι) T * rightTensor (ι₁ := ι) G) := by
            rw [rightTensor_mul_rightTensor]
    _ = (commuteGHalfSandwich_moveStepTargetFamily params family r
          ((moveTailQuestionEquiv params r) q)).outcome
          ((moveTailOutcomeEquiv params r) ogs) := by
            simp [commuteGHalfSandwich_moveStepTargetFamily, moveTailQuestionEquiv,
              moveTailOutcomeEquiv, A, B, T, G, mul_assoc]









lemma commuteGHalfSandwich_moveChainLift_moveFamily_eq_moveStepMid
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ)
    (q : MoveQ params (r + 1))
    (ogs : MoveO params (r + 1)) :
    (commuteGHalfSandwich_moveChainLiftFamily params family r
      (commuteGHalfSandwich_moveFamily params family r) q).outcome
        ogs =
      (commuteGHalfSandwich_moveStepMidFamily params family r
        ((moveTailQuestionEquiv params r) q)).outcome
        ((moveTailOutcomeEquiv params r) ogs) := by
  let A := (gHatIdxMeas params family q.1).outcome ogs.1
  let B := (gHatIdxMeas params family q.2.1).outcome ogs.2.1
  let G := (gHatIdxMeas params family (q.2.2 0)).outcome (ogs.2.2 0)
  let T := gHatReverseHalfProductOutcomeOperator params family r
    (pointTupleTail q.2.2) (gHatTupleOutcomeTail ogs.2.2)
  calc
    (commuteGHalfSandwich_moveChainLiftFamily params family r
      (commuteGHalfSandwich_moveFamily params family r) q).outcome ogs
      = leftTensor (ι₂ := ι) A *
          (leftTensor (ι₂ := ι) (B * G) * rightTensor (ι₁ := ι) T) := by
            simp [commuteGHalfSandwich_moveChainLiftFamily, commuteGHalfSandwich_moveFamily,
              A, B, G, T,
              leftTensor_mul_leftTensor]
    _ =
        (leftTensor (ι₂ := ι) A * leftTensor (ι₂ := ι) (B * G)) *
          rightTensor (ι₁ := ι) T := by
          simp [mul_assoc]
    _ = leftTensor (ι₂ := ι) (A * (B * G)) * rightTensor (ι₁ := ι) T := by
          rw [leftTensor_mul_leftTensor]
    _ = (commuteGHalfSandwich_moveStepMidFamily params family r
          ((moveTailQuestionEquiv params r) q)).outcome
          ((moveTailOutcomeEquiv params r) ogs) := by
            simp [commuteGHalfSandwich_moveStepMidFamily, moveTailQuestionEquiv,
              moveTailOutcomeEquiv, A, B, G, T, leftTensor_mul_leftTensor, mul_assoc]





end MIPStarRE.LDT.Pasting

end

end LIDT

open LIDT
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

open LIDT.MIPStarRE.LDT.Pasting

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

theorem solution
    (params : _root_.LIDT.MIPStarRE.LDT.Parameters) [_root_.LIDT.MIPStarRE.LDT.FieldModel params.q]
    (ψbi : _root_.LIDT.MIPStarRE.LDT.QuantumState (ι × ι))
    (family : _root_.LIDT.MIPStarRE.LDT.IdxPolyFamily params ι)
    (zeta : _root_.LIDT.MIPStarRE.LDT.Error) (r : ℕ)
    (hsc : _root_.LIDT.MIPStarRE.LDT.SDDRel ψbi
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params))
      (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatSelfConsistencyLeftFamily params family)
      (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatSelfConsistencyRightFamily params family)
      (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatSelfConsistencyError zeta)) :
    _root_.LIDT.MIPStarRE.LDT.SDDOpRel ψbi
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.MoveQ params (r + 1)))
      (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_moveChainLiftFamily params family r
        (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_moveFamily params family r))
      (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_moveFamily params family (r + 1))
      (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatSelfConsistencyError zeta) := by
  have hmid :
      _root_.LIDT.MIPStarRE.LDT.SDDOpRel ψbi
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.MoveQ params (r + 1)))
        (fun q => _root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_moveStepMidFamily params family r
          ((_root_.LIDT.MIPStarRE.LDT.Pasting.moveTailQuestionEquiv params r) q))
        (fun q => _root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_moveStepTargetFamily params family r
          ((_root_.LIDT.MIPStarRE.LDT.Pasting.moveTailQuestionEquiv params r) q))
        (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatSelfConsistencyError zeta) :=
    (_root_.LIDT.MIPStarRE.LDT.Pasting.sddOpRel_uniform_equiv (_root_.LIDT.MIPStarRE.LDT.Pasting.moveTailQuestionEquiv params r) ψbi
      (fun q => _root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_moveStepMidFamily params family r
        ((_root_.LIDT.MIPStarRE.LDT.Pasting.moveTailQuestionEquiv params r) q))
      (fun q => _root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_moveStepTargetFamily params family r
        ((_root_.LIDT.MIPStarRE.LDT.Pasting.moveTailQuestionEquiv params r) q))
      (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatSelfConsistencyError zeta)).2
      (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_moveStepMid_toTarget params ψbi family zeta r hsc)
  have hreindex := _root_.LIDT.MIPStarRE.LDT.CommutativityPoints.sddOpRel_reindex (_root_.LIDT.MIPStarRE.LDT.Pasting.moveTailOutcomeEquiv params r).symm
    ψbi
    (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.MoveQ params (r + 1)))
    (fun q => _root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_moveStepMidFamily params family r
      ((_root_.LIDT.MIPStarRE.LDT.Pasting.moveTailQuestionEquiv params r) q))
    (fun q => _root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_moveStepTargetFamily params family r
      ((_root_.LIDT.MIPStarRE.LDT.Pasting.moveTailQuestionEquiv params r) q))
    (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatSelfConsistencyError zeta)
    hmid
  exact _root_.LIDT.MIPStarRE.LDT.CommutativityPoints.sddOpRel_congr_outcome ψbi
    (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.MoveQ params (r + 1)))
    _ _
    (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_moveChainLiftFamily params family r
      (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_moveFamily params family r))
    (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_moveFamily params family (r + 1))
    (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatSelfConsistencyError zeta)
    (fun q ogs => by
      simpa [_root_.LIDT.MIPStarRE.LDT.Pasting.moveTailQuestionEquiv, _root_.LIDT.MIPStarRE.LDT.Pasting.moveTailOutcomeEquiv] using
        (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_moveChainLift_moveFamily_eq_moveStepMid params family r q ogs).symm)
    (fun q ogs => by
      simpa [_root_.LIDT.MIPStarRE.LDT.Pasting.moveTailQuestionEquiv, _root_.LIDT.MIPStarRE.LDT.Pasting.moveTailOutcomeEquiv] using
        (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_moveFamily_eq_moveStepTarget params family r q ogs).symm)
    hreindex
