-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_split_succ_iff
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T16:09:08.352376+00:00
-- url     : https://prove2.me/submissions/68835200-fc06-4df9-a05a-cc07d048fde2

-- Generated proof for MIPStarRE.LDT.Pasting.commuteGHalfSandwich_split_succ_iff.
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
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_commuteGHalfSandwich_moveSource_eq_split
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

/- Source helpers from MIPStarRE/LDT/Pasting/ComparisonLemmas/CommuteGHalfSandwich/MoveChain/Base.lean. -/
/-!
# Section 12 pasting: half-sandwich move-chain base

This module introduces the question and outcome types used by the finite
commutation chain in `lem:commute-g-half-sandwich`.  It also defines the first
recursive target family and proves the equivalence between the source
split-successor comparison and the first move-chain comparison.

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

/-! ## Recursive target family and the split-succ equivalence

These are the basic building blocks for the half-sandwich commutation chain:
type abbreviations, the recursive target family, and the split-succ equivalence
(`split_succ_iff`) plus the prefix-second-slice-left lemma.
-/










lemma commuteGHalfSandwich_recursiveTarget_eq_split
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ)
    (q : MoveQ params r)
    (ogs : MoveO params r) :
    (commuteGHalfSandwich_recursiveTargetFamily params family r q).outcome
      ogs =
      (headTailRotatedFamily params family (r + 1) (q.1, Fin.cons q.2.1 q.2.2)).outcome
        (ogs.1, Fin.cons ogs.2.1 ogs.2.2) := by
  let A := (gHatIdxMeas params family q.2.1).outcome ogs.2.1
  let T := gHatHalfProductOutcomeOperator params family r q.2.2 ogs.2.2
  let G := (gHatIdxMeas params family q.1).outcome ogs.1
  have htail :
      T = gHatHalfProductOutcomeOperator params family r
        (pointTupleTail (Fin.cons q.2.1 q.2.2))
        (gHatTupleOutcomeTail (Fin.cons ogs.2.1 ogs.2.2)) := by
    rfl
  calc
    (commuteGHalfSandwich_recursiveTargetFamily params family r q).outcome ogs
      = leftTensor (ι₂ := ι) (A * (T * G)) := by
          simp [commuteGHalfSandwich_recursiveTargetFamily, headTailRotatedFamily,
            A, T, G, leftTensor_mul_leftTensor]
    _ = leftTensor (ι₂ := ι)
          (A * (gHatHalfProductOutcomeOperator params family r
            (pointTupleTail (Fin.cons q.2.1 q.2.2))
            (gHatTupleOutcomeTail (Fin.cons ogs.2.1 ogs.2.2)) * G)) := by
              exact congrArg (fun X => leftTensor (ι₂ := ι) (A * (X * G))) htail.symm
    _ = (headTailRotatedFamily params family (r + 1) (q.1, Fin.cons q.2.1 q.2.2)).outcome
          (ogs.1, Fin.cons ogs.2.1 ogs.2.2) := by
            simp [headTailRotatedFamily, A, G, gHatHalfProductOutcomeOperator,
               leftTensor_mul_leftTensor, mul_assoc]



end MIPStarRE.LDT.Pasting

end

end LIDT

open LIDT
/-!
# Section 12 pasting: half-sandwich move-chain base

This module introduces the question and outcome types used by the finite
commutation chain in `lem:commute-g-half-sandwich`.  It also defines the first
recursive target family and proves the equivalence between the source
split-successor comparison and the first move-chain comparison.

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

/-! ## Recursive target family and the split-succ equivalence

These are the basic building blocks for the half-sandwich commutation chain:
type abbreviations, the recursive target family, and the split-succ equivalence
(`split_succ_iff`) plus the prefix-second-slice-left lemma.
-/

theorem solution
    (params : _root_.LIDT.MIPStarRE.LDT.Parameters) [_root_.LIDT.MIPStarRE.LDT.FieldModel params.q]
    (ψbi : _root_.LIDT.MIPStarRE.LDT.QuantumState (ι × ι))
    (family : _root_.LIDT.MIPStarRE.LDT.IdxPolyFamily params ι) (r : ℕ) (δ : _root_.LIDT.MIPStarRE.LDT.Error) :
    _root_.LIDT.MIPStarRE.LDT.SDDOpRel ψbi
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params × _root_.LIDT.MIPStarRE.LDT.PointTuple params (r + 1)))
      (_root_.LIDT.MIPStarRE.LDT.Pasting.headTailOrderedFamily params family (r + 1))
      (_root_.LIDT.MIPStarRE.LDT.Pasting.headTailRotatedFamily params family (r + 1))
      δ ↔
    _root_.LIDT.MIPStarRE.LDT.SDDOpRel ψbi
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.MoveQ params r))
      (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_moveSourceFamily params family r)
      (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_recursiveTargetFamily params family r)
      δ := by
  constructor
  · intro h
    have hq :=
      (_root_.LIDT.MIPStarRE.LDT.Pasting.sddOpRel_uniform_equiv (_root_.LIDT.MIPStarRE.LDT.Pasting.splitSuccQuestionEquiv params r) ψbi
        (_root_.LIDT.MIPStarRE.LDT.Pasting.headTailOrderedFamily params family (r + 1))
        (_root_.LIDT.MIPStarRE.LDT.Pasting.headTailRotatedFamily params family (r + 1)) δ).1 h
    have ho := _root_.LIDT.MIPStarRE.LDT.CommutativityPoints.sddOpRel_reindex (_root_.LIDT.MIPStarRE.LDT.Pasting.splitSuccOutcomeEquiv params r)
      ψbi
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.MoveQ params r))
      (fun q =>
        _root_.LIDT.MIPStarRE.LDT.Pasting.headTailOrderedFamily params family (r + 1) ((_root_.LIDT.MIPStarRE.LDT.Pasting.splitSuccQuestionEquiv params r).symm q))
      (fun q =>
        _root_.LIDT.MIPStarRE.LDT.Pasting.headTailRotatedFamily params family (r + 1) ((_root_.LIDT.MIPStarRE.LDT.Pasting.splitSuccQuestionEquiv params r).symm q))
      δ hq
    exact _root_.LIDT.MIPStarRE.LDT.CommutativityPoints.sddOpRel_congr_outcome ψbi
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.MoveQ params r))
      _ _
      (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_moveSourceFamily params family r)
      (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_recursiveTargetFamily params family r)
      δ
      (fun q ogs => by
        simpa [_root_.LIDT.MIPStarRE.LDT.Pasting.splitSuccQuestionEquiv, _root_.LIDT.MIPStarRE.LDT.Pasting.splitSuccOutcomeEquiv] using
          (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_moveSource_eq_split params family r
            q
            ogs).symm)
      (fun q ogs => by
        simpa [_root_.LIDT.MIPStarRE.LDT.Pasting.splitSuccQuestionEquiv, _root_.LIDT.MIPStarRE.LDT.Pasting.splitSuccOutcomeEquiv] using
          (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_recursiveTarget_eq_split params family r
            q
            ogs).symm)
      ho
  · intro h
    have ho := _root_.LIDT.MIPStarRE.LDT.CommutativityPoints.sddOpRel_reindex (_root_.LIDT.MIPStarRE.LDT.Pasting.splitSuccOutcomeEquiv params r).symm
      ψbi
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.MoveQ params r))
      (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_moveSourceFamily params family r)
      (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_recursiveTargetFamily params family r)
      δ h
    have hq := _root_.LIDT.MIPStarRE.LDT.CommutativityPoints.sddOpRel_congr_outcome ψbi
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.MoveQ params r))
      _ _
      (fun q =>
        _root_.LIDT.MIPStarRE.LDT.Pasting.headTailOrderedFamily params family (r + 1) ((_root_.LIDT.MIPStarRE.LDT.Pasting.splitSuccQuestionEquiv params r).symm q))
      (fun q =>
        _root_.LIDT.MIPStarRE.LDT.Pasting.headTailRotatedFamily params family (r + 1) ((_root_.LIDT.MIPStarRE.LDT.Pasting.splitSuccQuestionEquiv params r).symm q))
      δ
      (fun q ogs => by
        have hogs : (ogs.1, Fin.cons (ogs.2 0) (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleOutcomeTail ogs.2)) = ogs :=
          (_root_.LIDT.MIPStarRE.LDT.Pasting.splitSuccOutcomeEquiv params r).left_inv ogs
        simpa [_root_.LIDT.MIPStarRE.LDT.Pasting.splitSuccQuestionEquiv, _root_.LIDT.MIPStarRE.LDT.Pasting.splitSuccOutcomeEquiv, hogs] using
          (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_moveSource_eq_split params family r
            q ((_root_.LIDT.MIPStarRE.LDT.Pasting.splitSuccOutcomeEquiv params r) ogs)))
      (fun q ogs => by
        have hogs : (ogs.1, Fin.cons (ogs.2 0) (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleOutcomeTail ogs.2)) = ogs :=
          (_root_.LIDT.MIPStarRE.LDT.Pasting.splitSuccOutcomeEquiv params r).left_inv ogs
        simpa [_root_.LIDT.MIPStarRE.LDT.Pasting.splitSuccQuestionEquiv, _root_.LIDT.MIPStarRE.LDT.Pasting.splitSuccOutcomeEquiv, hogs] using
          (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_recursiveTarget_eq_split params family r
            q ((_root_.LIDT.MIPStarRE.LDT.Pasting.splitSuccOutcomeEquiv params r) ogs)))
      ho
    exact (_root_.LIDT.MIPStarRE.LDT.Pasting.sddOpRel_uniform_equiv (_root_.LIDT.MIPStarRE.LDT.Pasting.splitSuccQuestionEquiv params r) ψbi
      (_root_.LIDT.MIPStarRE.LDT.Pasting.headTailOrderedFamily params family (r + 1))
      (_root_.LIDT.MIPStarRE.LDT.Pasting.headTailRotatedFamily params family (r + 1)) δ).2 hq
