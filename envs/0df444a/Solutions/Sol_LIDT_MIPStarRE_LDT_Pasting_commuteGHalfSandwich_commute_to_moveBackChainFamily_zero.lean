-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_commute_to_moveBackChainFamily_zero
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T17:19:23.315733+00:00
-- url     : https://prove2.me/submissions/0a9c144d-d87b-471f-84e5-6fe9b8958688

-- Generated proof for MIPStarRE.LDT.Pasting.commuteGHalfSandwich_commute_to_moveBackChainFamily_zero.
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
import Theorems.Thm_LIDT_MIPStarRE_LDT_Preliminaries_qSDDOp_symm

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

/- Source helpers from MIPStarRE/LDT/Pasting/ComparisonLemmas/CommuteGHalfSandwich/MoveChain/BackChain.lean. -/
/-!
# Section 12 pasting: half-sandwich move-back chain

This module contains the reverse part of the finite commutation chain used in
`lem:commute-g-half-sandwich`.  After the initial move chain and the flat
post-move comparison, these families bring the leading completed-slice
measurement back to the position required by the rotated half-sandwich endpoint.

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


/-! ## Move-back chain

The `moveBackChainFamily` and its endpoint lemmas reverse the commutation to
bring the leading `Ĝ` back into position.
-/



lemma commuteGHalfSandwich_secondSliceLift_moveFamily_eq_swappedFrontMoveStepMid
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ)
    (q : MoveQ params (r + 1))
    (ogs : MoveO params (r + 1)) :
    (commuteGHalfSandwich_secondSliceLiftFamily params family r
      (commuteGHalfSandwich_moveFamily params family r) q).outcome
        ogs =
      (commuteGHalfSandwich_moveStepMidFamily params family r
        ((moveTailSwappedFrontQuestionEquiv params r) q)).outcome
        ((moveTailSwappedFrontOutcomeEquiv params r) ogs) := by
  let A := (gHatIdxMeas params family q.2.1).outcome ogs.2.1
  let B := (gHatIdxMeas params family q.1).outcome ogs.1
  let G := (gHatIdxMeas params family (q.2.2 0)).outcome (ogs.2.2 0)
  let T := gHatReverseHalfProductOutcomeOperator params family r
    (pointTupleTail q.2.2) (gHatTupleOutcomeTail ogs.2.2)
  calc
    (commuteGHalfSandwich_secondSliceLiftFamily params family r
      (commuteGHalfSandwich_moveFamily params family r) q).outcome ogs
      = leftTensor (ι₂ := ι) A *
          (leftTensor (ι₂ := ι) (B * G) * rightTensor (ι₁ := ι) T) := by
            simp [commuteGHalfSandwich_secondSliceLiftFamily, commuteGHalfSandwich_moveFamily,
              A, B, G, T, leftTensor_mul_leftTensor]
    _ =
        (leftTensor (ι₂ := ι) A * leftTensor (ι₂ := ι) (B * G)) *
          rightTensor (ι₁ := ι) T := by
          simp [mul_assoc]
    _ = leftTensor (ι₂ := ι) (A * (B * G)) * rightTensor (ι₁ := ι) T := by
          rw [leftTensor_mul_leftTensor]
    _ = (commuteGHalfSandwich_moveStepMidFamily params family r
          ((moveTailSwappedFrontQuestionEquiv params r) q)).outcome
          ((moveTailSwappedFrontOutcomeEquiv params r) ogs) := by
            simp [commuteGHalfSandwich_moveStepMidFamily,
              moveTailSwappedFrontQuestionEquiv, moveTailSwappedFrontOutcomeEquiv,
              moveTailQuestionEquiv, moveTailOutcomeEquiv,
              swappedFrontQuestionEquiv, swappedFrontOutcomeEquiv,
              A, B, G, T, leftTensor_mul_leftTensor, mul_assoc]

lemma commuteGHalfSandwich_commute_eq_swappedFrontMoveStepTarget
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ)
    (q : MoveQ params (r + 1))
    (ogs : MoveO params (r + 1)) :
    (commuteGHalfSandwich_commuteFamily params family (r + 1) q).outcome
      ogs =
      (commuteGHalfSandwich_moveStepTargetFamily params family r
        ((moveTailSwappedFrontQuestionEquiv params r) q)).outcome
        ((moveTailSwappedFrontOutcomeEquiv params r) ogs) := by
  simp [commuteGHalfSandwich_commuteFamily,
    moveTailSwappedFrontQuestionEquiv, moveTailSwappedFrontOutcomeEquiv,
    moveTailQuestionEquiv, moveTailOutcomeEquiv,
    swappedFrontQuestionEquiv, swappedFrontOutcomeEquiv,
    commuteGHalfSandwich_moveStepTargetFamily,
    gHatReverseHalfProductOutcomeOperator, leftTensor_mul_leftTensor,
    rightTensor_mul_rightTensor, mul_assoc]







end MIPStarRE.LDT.Pasting

end

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









/-- Symmetry of the operator-family state-dependent distance relation. -/
lemma sddOpRel_symm
    {Question Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι] [Fintype Outcome]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A B : IdxOpFamily Question Outcome ι) (δ : Error) :
    SDDOpRel ψ 𝒟 A B δ → SDDOpRel ψ 𝒟 B A δ := by
  intro ⟨h⟩
  constructor
  simpa [sddErrorOp, qSDDOp_symm] using h




end MIPStarRE.LDT.Preliminaries

end

end LIDT

open LIDT
/-!
# Section 12 pasting: half-sandwich move-back chain

This module contains the reverse part of the finite commutation chain used in
`lem:commute-g-half-sandwich`.  After the initial move chain and the flat
post-move comparison, these families bring the leading completed-slice
measurement back to the position required by the rotated half-sandwich endpoint.

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


/-! ## Move-back chain

The `moveBackChainFamily` and its endpoint lemmas reverse the commutation to
bring the leading `Ĝ` back into position.
-/

theorem solution
    (params : _root_.LIDT.MIPStarRE.LDT.Parameters) [_root_.LIDT.MIPStarRE.LDT.FieldModel params.q]
    (ψbi : _root_.LIDT.MIPStarRE.LDT.QuantumState (ι × ι))
    (family : _root_.LIDT.MIPStarRE.LDT.IdxPolyFamily params ι)
    (zeta : _root_.LIDT.MIPStarRE.LDT.Error) {r : ℕ}
    (hsc : _root_.LIDT.MIPStarRE.LDT.SDDRel ψbi
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params))
      (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatSelfConsistencyLeftFamily params family)
      (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatSelfConsistencyRightFamily params family)
      (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatSelfConsistencyError zeta)) :
    _root_.LIDT.MIPStarRE.LDT.SDDOpRel ψbi
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.MoveQ params (r + 1)))
      (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_commuteFamily params family (r + 1))
      ((_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_moveBackChainFamily params family r) 0)
      (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatSelfConsistencyError zeta) := by
  have htargetMid :
      _root_.LIDT.MIPStarRE.LDT.SDDOpRel ψbi
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.MoveTailQ params r))
        (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_moveStepTargetFamily params family r)
        (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_moveStepMidFamily params family r)
        (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatSelfConsistencyError zeta) :=
    _root_.LIDT.MIPStarRE.LDT.Preliminaries.sddOpRel_symm ψbi
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.MoveTailQ params r))
      (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_moveStepMidFamily params family r)
      (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_moveStepTargetFamily params family r)
      (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatSelfConsistencyError zeta)
      (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_moveStepMid_toTarget params ψbi family zeta r hsc)
  have hq :=
    (_root_.LIDT.MIPStarRE.LDT.Pasting.sddOpRel_uniform_equiv (_root_.LIDT.MIPStarRE.LDT.Pasting.moveTailSwappedFrontQuestionEquiv params r).symm ψbi
      (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_moveStepTargetFamily params family r)
      (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_moveStepMidFamily params family r)
      (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatSelfConsistencyError zeta)).1 htargetMid
  have ho := _root_.LIDT.MIPStarRE.LDT.CommutativityPoints.sddOpRel_reindex (_root_.LIDT.MIPStarRE.LDT.Pasting.moveTailSwappedFrontOutcomeEquiv params r).symm
    ψbi
    (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.MoveQ params (r + 1)))
    (fun q => _root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_moveStepTargetFamily params family r
      ((_root_.LIDT.MIPStarRE.LDT.Pasting.moveTailSwappedFrontQuestionEquiv params r) q))
    (fun q => _root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_moveStepMidFamily params family r
      ((_root_.LIDT.MIPStarRE.LDT.Pasting.moveTailSwappedFrontQuestionEquiv params r) q))
    (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatSelfConsistencyError zeta)
    hq
  exact _root_.LIDT.MIPStarRE.LDT.CommutativityPoints.sddOpRel_congr_outcome ψbi
    (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.MoveQ params (r + 1)))
    _ _
    (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_commuteFamily params family (r + 1))
    ((_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_moveBackChainFamily params family r) 0)
    (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatSelfConsistencyError zeta)
    (fun q ogs => by
      simpa using
        (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_commute_eq_swappedFrontMoveStepTarget params family r q ogs).symm)
    (fun q ogs => by
      let q' : _root_.LIDT.MIPStarRE.LDT.Pasting.MoveQ params r :=
        (q.1, q.2.2 0, _root_.LIDT.MIPStarRE.LDT.Pasting.pointTupleTail q.2.2)
      let ogs' : _root_.LIDT.MIPStarRE.LDT.Pasting.MoveO params r :=
        (ogs.1, ogs.2.2 0, _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleOutcomeTail ogs.2.2)
      have hlast :
          (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_moveBackChainFamily params family r 0 q).outcome
            ogs =
            (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_secondSliceLiftFamily params family r
              (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_moveFamily params family r) q).outcome ogs := by
        let G := (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.2.1).outcome ogs.2.1
        have hidx : (⟨r - (0 : Fin (r + 1)).1, by omega⟩ : Fin (r + 1)) =
            Fin.last r := by
          ext
          simp
        calc
          (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_moveBackChainFamily params family r 0 q).outcome ogs
            = _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) G *
                (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_moveChainFamily params family r
                  (⟨r - (0 : Fin (r + 1)).1, by omega⟩ : Fin (r + 1)) q').outcome
                  ogs' := by
                  simp [_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_moveBackChainFamily,
                    _root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_secondSliceLiftFamily, q', ogs', G]
          _ = _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) G *
                (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_moveChainFamily params family r (Fin.last r) q').outcome
                  ogs' := by
                  rw [hidx]
          _ = _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) G *
                (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_moveFamily params family r q').outcome ogs' := by
                  exact congrArg (fun X => _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) G * X)
                    (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_moveChainFamily_last params family r q' ogs')
          _ = (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_secondSliceLiftFamily params family r
                (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_moveFamily params family r) q).outcome ogs := by
                rfl
      calc
        (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_moveStepMidFamily params family r
          ((_root_.LIDT.MIPStarRE.LDT.Pasting.moveTailSwappedFrontQuestionEquiv params r) q)).outcome
          ((_root_.LIDT.MIPStarRE.LDT.Pasting.moveTailSwappedFrontOutcomeEquiv params r) ogs)
            = (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_secondSliceLiftFamily params family r
                (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_moveFamily params family r) q).outcome ogs := by
                  exact (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_secondSliceLift_moveFamily_eq_swappedFrontMoveStepMid
                    params family r q ogs).symm
        _ = (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_moveBackChainFamily params family r 0 q).outcome ogs := by
              simpa using hlast.symm)
    ho
