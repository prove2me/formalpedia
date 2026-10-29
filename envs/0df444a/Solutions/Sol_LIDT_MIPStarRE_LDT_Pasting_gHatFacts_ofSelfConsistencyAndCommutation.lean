-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Pasting.gHatFacts_ofSelfConsistencyAndCommutation
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T17:19:23.421595+00:00
-- url     : https://prove2.me/submissions/b67112ac-d5a8-48c7-9214-f85d8ad219a8

-- Generated proof for MIPStarRE.LDT.Pasting.gHatFacts_ofSelfConsistencyAndCommutation.
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
import Theorems.Thm_LIDT_MIPStarRE_LDT_Preliminaries_qSDDOp_symm

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

/- Source helpers from MIPStarRE/LDT/Pasting/GHatFacts.lean. -/
/-!
# Section 12 pasting: G-hat facts

Quadrant decompositions and `GHat` bookkeeping facts.
-/

@[expose] public section

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The pointwise `\widehat G` pair product splits into the complete-complete,
complete-incomplete, incomplete-complete, and incomplete-incomplete quadrants. -/
private lemma gHatPairProduct_qSDDOp_decompose
    (params : Parameters)
    [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (q : SlicePairQuestion params) :
    qSDDOp ψbi
        (gHatPairProductLeft params family q)
        (gHatPairProductRight params family q) =
      qSDDOp ψbi
          (OpFamily.leftPlacedOpFamily (ιB := ι) <|
            orderedProductOpFamily
              ((family.meas q.1).toSubMeas)
              ((family.meas q.2).toSubMeas))
          (OpFamily.leftPlacedOpFamily (ιB := ι) <|
            reversedProductOpFamily
              ((family.meas q.1).toSubMeas)
              ((family.meas q.2).toSubMeas)) +
        qSDDOp ψbi
          (incompletePartPointProductLeft params family q)
          (incompletePartPointProductRight params family q) +
          qSDDOp ψbi
            (OpFamily.leftPlacedOpFamily (ιB := ι) <|
              multiplyByTotalOnLeft
                (incompletePartSubMeas params family q.1)
                ((family.meas q.2).toSubMeas))
            (OpFamily.leftPlacedOpFamily (ιB := ι) <|
              multiplyByTotalOnRight
                ((family.meas q.2).toSubMeas)
                (incompletePartSubMeas params family q.1)) +
        qSDDOp ψbi
          (incompletePartTotalProductLeft params family q)
          (incompletePartTotalProductRight params family q) := by
  rcases q with ⟨x, y⟩
  let completeLeft :
      (Polynomial params × Polynomial params) → MIPStarRE.Quantum.Op (ι × ι) :=
    (OpFamily.leftPlacedOpFamily (ιB := ι) <|
      orderedProductOpFamily
        ((family.meas x).toSubMeas)
        ((family.meas y).toSubMeas)).outcome
  let completeRight :
      (Polynomial params × Polynomial params) → MIPStarRE.Quantum.Op (ι × ι) :=
    (OpFamily.leftPlacedOpFamily (ιB := ι) <|
      reversedProductOpFamily
        ((family.meas x).toSubMeas)
        ((family.meas y).toSubMeas)).outcome
  let incompleteLeft : Polynomial params → MIPStarRE.Quantum.Op (ι × ι) :=
    (incompletePartPointProductLeft params family (x, y)).outcome
  let incompleteRight : Polynomial params → MIPStarRE.Quantum.Op (ι × ι) :=
    (incompletePartPointProductRight params family (x, y)).outcome
  let swappedLeft : Polynomial params → MIPStarRE.Quantum.Op (ι × ι) :=
    (OpFamily.leftPlacedOpFamily (ιB := ι) <|
      multiplyByTotalOnLeft
        (incompletePartSubMeas params family x)
        ((family.meas y).toSubMeas)).outcome
  let swappedRight : Polynomial params → MIPStarRE.Quantum.Op (ι × ι) :=
    (OpFamily.leftPlacedOpFamily (ιB := ι) <|
      multiplyByTotalOnRight
        ((family.meas y).toSubMeas)
        (incompletePartSubMeas params family x)).outcome
  let totalLeft : Unit → MIPStarRE.Quantum.Op (ι × ι) :=
    (incompletePartTotalProductLeft params family (x, y)).outcome
  let totalRight : Unit → MIPStarRE.Quantum.Op (ι × ι) :=
    (incompletePartTotalProductRight params family (x, y)).outcome
  let gHatLeft :
      Option (Polynomial params) × Option (Polynomial params) →
        MIPStarRE.Quantum.Op (ι × ι) :=
    fun ab =>
      match ab.1, ab.2 with
      | some g, some h => completeLeft (g, h)
      | some g, none => incompleteLeft g
      | none, some h => swappedLeft h
      | none, none => totalLeft ()
  let gHatRight :
      Option (Polynomial params) × Option (Polynomial params) →
        MIPStarRE.Quantum.Op (ι × ι) :=
    fun ab =>
      match ab.1, ab.2 with
      | some g, some h => completeRight (g, h)
      | some g, none => incompleteRight g
      | none, some h => swappedRight h
      | none, none => totalRight ()
  have hgHatLeft :
      (gHatPairProductLeft params family (x, y)).outcome = gHatLeft := by
    funext ab
    rcases ab with ⟨a, b⟩
    cases a <;> cases b <;>
      simp [gHatLeft, completeLeft, incompleteLeft, swappedLeft, totalLeft,
        gHatPairProductLeft, gHatIdxMeas, completeSubMeas,
        incompletePartPointProductLeft, incompletePartTotalProductLeft,
        incompletePartSubMeas, multiplyByTotalOnLeft, multiplyByTotalOnRight,
        orderedProductOpFamily, OpFamily.leftPlacedOpFamily]
  have hgHatRight :
      (gHatPairProductRight params family (x, y)).outcome = gHatRight := by
    funext ab
    rcases ab with ⟨a, b⟩
    cases a <;> cases b <;>
      simp [gHatRight, completeRight, incompleteRight, swappedRight, totalRight,
        gHatPairProductRight, gHatIdxMeas, completeSubMeas,
        incompletePartPointProductRight, incompletePartTotalProductRight,
        incompletePartSubMeas, multiplyByTotalOnLeft, multiplyByTotalOnRight,
        reversedProductOpFamily, OpFamily.leftPlacedOpFamily]
  calc
    qSDDOp ψbi
        (gHatPairProductLeft params family (x, y))
        (gHatPairProductRight params family (x, y))
      =
        qSDDCore ψbi
          (fun ab : Option (Polynomial params) × Option (Polynomial params) =>
            match ab.1, ab.2 with
            | some g, some h => completeLeft (g, h)
            | some g, none => incompleteLeft g
            | none, some h => swappedLeft h
            | none, none => totalLeft ())
          (fun ab : Option (Polynomial params) × Option (Polynomial params) =>
            match ab.1, ab.2 with
            | some g, some h => completeRight (g, h)
            | some g, none => incompleteRight g
            | none, some h => swappedRight h
            | none, none => totalRight ()) := by
          rw [qSDDOp, hgHatLeft, hgHatRight]
    _ =
        qSDDCore ψbi completeLeft completeRight +
          qSDDCore ψbi incompleteLeft incompleteRight +
          qSDDCore ψbi swappedLeft swappedRight +
          qSDDCore ψbi totalLeft totalRight := by
            unfold qSDDCore
            trans
              (∑ ab : Option (Polynomial params) × Option (Polynomial params),
                match ab.1, ab.2 with
                | some g, some h =>
                    ev ψbi ((completeLeft (g, h) - completeRight (g, h))ᴴ *
                      (completeLeft (g, h) - completeRight (g, h)))
                | some g, none =>
                    ev ψbi ((incompleteLeft g - incompleteRight g)ᴴ *
                      (incompleteLeft g - incompleteRight g))
                | none, some h =>
                    ev ψbi ((swappedLeft h - swappedRight h)ᴴ *
                      (swappedLeft h - swappedRight h))
                | none, none =>
                    ev ψbi ((totalLeft () - totalRight ())ᴴ *
                      (totalLeft () - totalRight ())))
            · apply Finset.sum_congr rfl
              rintro ⟨og, oh⟩ _hmem
              cases og <;> cases oh <;> rfl
            · have htotal :
                  (∑ a : Unit,
                    ev ψbi ((totalLeft a - totalRight a)ᴴ *
                      (totalLeft a - totalRight a))) =
                  ev ψbi ((totalLeft () - totalRight ())ᴴ *
                    (totalLeft () - totalRight ())) := by
                simp
              rw [htotal]
              rw [Fintype.sum_prod_type, Fintype.sum_option]
              simp_rw [Fintype.sum_option]
              rw [Finset.sum_add_distrib, ← Fintype.sum_prod_type']
              abel
    _ =
        qSDDOp ψbi
            (OpFamily.leftPlacedOpFamily (ιB := ι) <|
              orderedProductOpFamily
                ((family.meas x).toSubMeas)
                ((family.meas y).toSubMeas))
            (OpFamily.leftPlacedOpFamily (ιB := ι) <|
              reversedProductOpFamily
                ((family.meas x).toSubMeas)
                ((family.meas y).toSubMeas)) +
          qSDDOp ψbi
            (incompletePartPointProductLeft params family (x, y))
            (incompletePartPointProductRight params family (x, y)) +
            qSDDOp ψbi
              (OpFamily.leftPlacedOpFamily (ιB := ι) <|
                multiplyByTotalOnLeft
                  (incompletePartSubMeas params family x)
                  ((family.meas y).toSubMeas))
              (OpFamily.leftPlacedOpFamily (ιB := ι) <|
                multiplyByTotalOnRight
                  ((family.meas y).toSubMeas)
                  (incompletePartSubMeas params family x)) +
          qSDDOp ψbi
            (incompletePartTotalProductLeft params family (x, y))
            (incompletePartTotalProductRight params family (x, y)) := rfl







end MIPStarRE.LDT.Pasting

end

end LIDT

open LIDT
/-!
# Section 12 pasting: G-hat facts

Quadrant decompositions and `GHat` bookkeeping facts.
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
    (ψbi : _root_.LIDT.MIPStarRE.LDT.QuantumState (ι × ι))
    (family : _root_.LIDT.MIPStarRE.LDT.IdxPolyFamily params ι)
    (gamma zeta : _root_.LIDT.MIPStarRE.LDT.Error)
    (hgamma_nonneg : 0 ≤ gamma) (hgamma : gamma ≤ 1)
    (_hzeta_nonneg : 0 ≤ zeta) (hzeta : zeta ≤ 1)
    (hd_le_q : params.d ≤ params.q)
    (hselfComplete : _root_.LIDT.MIPStarRE.LDT.Pasting.GCompleteSelfConsistencyStatement params ψbi family zeta)
    (hselfIncomplete : _root_.LIDT.MIPStarRE.LDT.Pasting.GBotSelfConsistencyStatement params ψbi family zeta)
    (hcommComplete : _root_.LIDT.MIPStarRE.LDT.Pasting.CommutingWithGCompleteStatement params ψbi family gamma zeta)
    (hcommIncomplete : _root_.LIDT.MIPStarRE.LDT.Pasting.CommutingWithGIncompleteStatement params ψbi family gamma zeta) :
    _root_.LIDT.MIPStarRE.LDT.Pasting.GHatFactsStatement params ψbi family gamma zeta := by
  refine {
    completedSelfConsistency := ?_
    completedCommutation := ?_
  }
  · -- Paper reference: `cor:G-hat-facts` in `ld-pasting.tex`.
    -- This step needs the full slice-family self-consistency witness:
    -- `\widehat G` expands into the original slice outcomes together with the
    -- incomplete part, not into the postprocessed complete-part family alone.
    rcases hselfComplete.completePartSelfConsistency with ⟨hcomplete_bound⟩
    rcases hselfIncomplete.incompletePartSelfConsistency with ⟨hincomplete_bound⟩
    refine ⟨?_⟩
    calc
      _root_.LIDT.MIPStarRE.LDT.sddError ψbi
          (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params))
          (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatSelfConsistencyLeftFamily params family)
          (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatSelfConsistencyRightFamily params family)
        =
          _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params))
            (fun x =>
              _root_.LIDT.MIPStarRE.LDT.qSDD ψbi
                  ((_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftLeft (_root_.LIDT.MIPStarRE.LDT.IdxProjSubMeas.toIdxSubMeas family.meas)) x)
                  ((_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftRight (_root_.LIDT.MIPStarRE.LDT.IdxProjSubMeas.toIdxSubMeas family.meas)) x) +
                _root_.LIDT.MIPStarRE.LDT.qSDD ψbi
                  ((_root_.LIDT.MIPStarRE.LDT.Pasting.incompletePartLeftFamily params family) x)
                  ((_root_.LIDT.MIPStarRE.LDT.Pasting.incompletePartRightFamily params family) x)) := by
            unfold _root_.LIDT.MIPStarRE.LDT.sddError
            apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
            intro x
            unfold _root_.LIDT.MIPStarRE.LDT.qSDD _root_.LIDT.MIPStarRE.LDT.qSDDCore
            rw [Fintype.sum_option]
            simp [_root_.LIDT.MIPStarRE.LDT.Pasting.gHatSelfConsistencyLeftFamily, _root_.LIDT.MIPStarRE.LDT.Pasting.gHatSelfConsistencyRightFamily,
              _root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas, _root_.LIDT.MIPStarRE.LDT.completeSubMeas, _root_.LIDT.MIPStarRE.LDT.Pasting.incompletePartLeftFamily,
              _root_.LIDT.MIPStarRE.LDT.Pasting.incompletePartRightFamily, _root_.LIDT.MIPStarRE.LDT.Pasting.incompletePartSubMeas, _root_.LIDT.MIPStarRE.LDT.leftPlacedSubMeas,
              _root_.LIDT.MIPStarRE.LDT.rightPlacedSubMeas,
              _root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftLeft, _root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftRight, _root_.LIDT.MIPStarRE.LDT.IdxProjSubMeas.toIdxSubMeas,
              add_comm]
      _ =
          _root_.LIDT.MIPStarRE.LDT.sddError ψbi
            (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params))
            (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftLeft (_root_.LIDT.MIPStarRE.LDT.IdxProjSubMeas.toIdxSubMeas family.meas))
            (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftRight (_root_.LIDT.MIPStarRE.LDT.IdxProjSubMeas.toIdxSubMeas family.meas)) +
          _root_.LIDT.MIPStarRE.LDT.sddError ψbi
            (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params))
            (_root_.LIDT.MIPStarRE.LDT.Pasting.incompletePartLeftFamily params family)
            (_root_.LIDT.MIPStarRE.LDT.Pasting.incompletePartRightFamily params family) := by
              rw [_root_.LIDT.MIPStarRE.LDT.sddError, _root_.LIDT.MIPStarRE.LDT.sddError, _root_.LIDT.MIPStarRE.LDT.avgOver_add]
      _ ≤ zeta + zeta := add_le_add hcomplete_bound hincomplete_bound
      _ = _root_.LIDT.MIPStarRE.LDT.Pasting.gHatSelfConsistencyError zeta := by
            simp [_root_.LIDT.MIPStarRE.LDT.Pasting.gHatSelfConsistencyError, two_mul]
  · -- Historical note (#199): `completedCommutation` is proved by splitting
    -- the gHat pair-product over `GHatOutcome × GHatOutcome` into complete,
    -- incomplete, swapped, and total quadrants, then bounding the sum by
    -- `gHatCommutationError`.
    -- Paper reference: `cor:G-hat-facts` in `ld-pasting.tex`.
    let swappedIncompletePointLeft :
        _root_.LIDT.MIPStarRE.LDT.IdxOpFamily (_root_.LIDT.MIPStarRE.LDT.Pasting.SlicePairQuestion params) (_root_.LIDT.MIPStarRE.LDT.Polynomial params) (ι × ι) :=
      fun q =>
        _root_.LIDT.MIPStarRE.LDT.OpFamily.leftPlacedOpFamily (ιB := ι) <|
          _root_.LIDT.MIPStarRE.LDT.Pasting.multiplyByTotalOnLeft
            (_root_.LIDT.MIPStarRE.LDT.Pasting.incompletePartSubMeas params family q.1)
            ((family.meas q.2).toSubMeas)
    let swappedIncompletePointRight :
        _root_.LIDT.MIPStarRE.LDT.IdxOpFamily (_root_.LIDT.MIPStarRE.LDT.Pasting.SlicePairQuestion params) (_root_.LIDT.MIPStarRE.LDT.Polynomial params) (ι × ι) :=
      fun q =>
        _root_.LIDT.MIPStarRE.LDT.OpFamily.leftPlacedOpFamily (ιB := ι) <|
          _root_.LIDT.MIPStarRE.LDT.Pasting.multiplyByTotalOnRight
            ((family.meas q.2).toSubMeas)
            (_root_.LIDT.MIPStarRE.LDT.Pasting.incompletePartSubMeas params family q.1)
    -- Alias for the shared `qSDDOp_symm` lemma, specializing to `(ι × ι)`.
    have hqSDDOp_symm_poly
        (A B : _root_.LIDT.MIPStarRE.LDT.OpFamily (_root_.LIDT.MIPStarRE.LDT.Polynomial params) (ι × ι)) :
        _root_.LIDT.MIPStarRE.LDT.qSDDOp ψbi A B = _root_.LIDT.MIPStarRE.LDT.qSDDOp ψbi B A := _root_.LIDT.MIPStarRE.LDT.Preliminaries.qSDDOp_symm ψbi A B
    have hswapIncompleteBound :
        _root_.LIDT.MIPStarRE.LDT.sddErrorOp ψbi
          (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SlicePairQuestion params))
          swappedIncompletePointLeft
          swappedIncompletePointRight
          ≤ _root_.LIDT.MIPStarRE.LDT.Pasting.commutingWithGIncompleteError params gamma zeta := by
      rcases hcommIncomplete.pointWithIncompletePartCommutation with ⟨hbound⟩
      calc
        _root_.LIDT.MIPStarRE.LDT.sddErrorOp ψbi
            (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SlicePairQuestion params))
            swappedIncompletePointLeft
            swappedIncompletePointRight
          =
            _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SlicePairQuestion params))
              (fun q =>
                _root_.LIDT.MIPStarRE.LDT.qSDDOp ψbi
                  (_root_.LIDT.MIPStarRE.LDT.Pasting.incompletePartPointProductLeft params family (q.2, q.1))
                  (_root_.LIDT.MIPStarRE.LDT.Pasting.incompletePartPointProductRight params family (q.2, q.1))) := by
                unfold _root_.LIDT.MIPStarRE.LDT.sddErrorOp swappedIncompletePointLeft swappedIncompletePointRight
                apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
                intro q
                rw [hqSDDOp_symm_poly]
                rfl
        _ =
            _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SlicePairQuestion params))
              (fun q =>
                _root_.LIDT.MIPStarRE.LDT.qSDDOp ψbi
                  (_root_.LIDT.MIPStarRE.LDT.Pasting.incompletePartPointProductLeft params family q)
                  (_root_.LIDT.MIPStarRE.LDT.Pasting.incompletePartPointProductRight params family q)) := by
                simpa [_root_.LIDT.MIPStarRE.LDT.Pasting.SlicePairQuestion, Prod.swap] using
                  (_root_.LIDT.MIPStarRE.LDT.avgOver_uniform_equiv
                    (Equiv.prodComm (_root_.LIDT.MIPStarRE.LDT.Fq params) (_root_.LIDT.MIPStarRE.LDT.Fq params))
                    (fun q =>
                      _root_.LIDT.MIPStarRE.LDT.qSDDOp ψbi
                        (_root_.LIDT.MIPStarRE.LDT.Pasting.incompletePartPointProductLeft params family q)
                        (_root_.LIDT.MIPStarRE.LDT.Pasting.incompletePartPointProductRight params family q))).symm
        _ =
            _root_.LIDT.MIPStarRE.LDT.sddErrorOp ψbi
              (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SlicePairQuestion params))
              (_root_.LIDT.MIPStarRE.LDT.Pasting.incompletePartPointProductLeft params family)
              (_root_.LIDT.MIPStarRE.LDT.Pasting.incompletePartPointProductRight params family) := by
                rfl
        _ ≤ _root_.LIDT.MIPStarRE.LDT.Pasting.commutingWithGIncompleteError params gamma zeta := hbound
    have hzeta_nonneg : 0 ≤ zeta := by
      rcases hselfIncomplete.incompletePartSelfConsistency with ⟨hbound⟩
      exact le_trans
        (_root_.LIDT.MIPStarRE.LDT.sddError_nonneg ψbi
          (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params))
          (_root_.LIDT.MIPStarRE.LDT.Pasting.incompletePartLeftFamily params family)
          (_root_.LIDT.MIPStarRE.LDT.Pasting.incompletePartRightFamily params family))
        hbound
    have hratio_nonneg : 0 ≤ ((params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error)) := by
      positivity
    have hratio_le_one : ((params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error)) ≤ 1 := by
      have hq_pos : (0 : _root_.LIDT.MIPStarRE.LDT.Error) < params.q := by
        exact_mod_cast params.hq
      exact (div_le_one hq_pos).2 (by simpa using hd_le_q)
    have hquarter_gamma :
        Real.rpow gamma (1 / (4 : _root_.LIDT.MIPStarRE.LDT.Error)) ≤ Real.rpow gamma (1 / (16 : _root_.LIDT.MIPStarRE.LDT.Error)) := by
      have hpow :
          (1 / (16 : _root_.LIDT.MIPStarRE.LDT.Error)) ≤ (1 / (4 : _root_.LIDT.MIPStarRE.LDT.Error)) := by norm_num
      exact Real.rpow_le_rpow_of_exponent_ge' hgamma_nonneg hgamma (by norm_num) hpow
    have hquarter_zeta :
        Real.rpow zeta (1 / (4 : _root_.LIDT.MIPStarRE.LDT.Error)) ≤ Real.rpow zeta (1 / (16 : _root_.LIDT.MIPStarRE.LDT.Error)) := by
      have hpow :
          (1 / (16 : _root_.LIDT.MIPStarRE.LDT.Error)) ≤ (1 / (4 : _root_.LIDT.MIPStarRE.LDT.Error)) := by norm_num
      exact Real.rpow_le_rpow_of_exponent_ge' hzeta_nonneg hzeta (by norm_num) hpow
    have hquarter_ratio :
        Real.rpow (((params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error))) (1 / (4 : _root_.LIDT.MIPStarRE.LDT.Error)) ≤
          Real.rpow (((params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error))) (1 / (16 : _root_.LIDT.MIPStarRE.LDT.Error)) := by
      have hpow :
          (1 / (16 : _root_.LIDT.MIPStarRE.LDT.Error)) ≤ (1 / (4 : _root_.LIDT.MIPStarRE.LDT.Error)) := by norm_num
      exact Real.rpow_le_rpow_of_exponent_ge' hratio_nonneg hratio_le_one (by norm_num) hpow
    let completeQuadrant : _root_.LIDT.MIPStarRE.LDT.Pasting.SlicePairQuestion params → _root_.LIDT.MIPStarRE.LDT.Error :=
      fun q =>
        _root_.LIDT.MIPStarRE.LDT.qSDDOp ψbi
          (_root_.LIDT.MIPStarRE.LDT.OpFamily.leftPlacedOpFamily (ιB := ι) <|
            _root_.LIDT.MIPStarRE.LDT.CommutativityPoints.orderedProductOpFamily
              ((family.meas q.1).toSubMeas)
              ((family.meas q.2).toSubMeas))
          (_root_.LIDT.MIPStarRE.LDT.OpFamily.leftPlacedOpFamily (ιB := ι) <|
            _root_.LIDT.MIPStarRE.LDT.CommutativityPoints.reversedProductOpFamily
              ((family.meas q.1).toSubMeas)
              ((family.meas q.2).toSubMeas))
    let incompleteQuadrant : _root_.LIDT.MIPStarRE.LDT.Pasting.SlicePairQuestion params → _root_.LIDT.MIPStarRE.LDT.Error :=
      fun q =>
        _root_.LIDT.MIPStarRE.LDT.qSDDOp ψbi
          (_root_.LIDT.MIPStarRE.LDT.Pasting.incompletePartPointProductLeft params family q)
          (_root_.LIDT.MIPStarRE.LDT.Pasting.incompletePartPointProductRight params family q)
    let swappedQuadrant : _root_.LIDT.MIPStarRE.LDT.Pasting.SlicePairQuestion params → _root_.LIDT.MIPStarRE.LDT.Error :=
      fun q =>
        _root_.LIDT.MIPStarRE.LDT.qSDDOp ψbi
          (swappedIncompletePointLeft q)
          (swappedIncompletePointRight q)
    let totalQuadrant : _root_.LIDT.MIPStarRE.LDT.Pasting.SlicePairQuestion params → _root_.LIDT.MIPStarRE.LDT.Error :=
      fun q =>
        _root_.LIDT.MIPStarRE.LDT.qSDDOp ψbi
          (_root_.LIDT.MIPStarRE.LDT.Pasting.incompletePartTotalProductLeft params family q)
          (_root_.LIDT.MIPStarRE.LDT.Pasting.incompletePartTotalProductRight params family q)
    have hdecomp_q :
        ∀ q,
          _root_.LIDT.MIPStarRE.LDT.qSDDOp ψbi
              (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatPairProductLeft params family q)
              (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatPairProductRight params family q) =
            completeQuadrant q +
              incompleteQuadrant q +
              swappedQuadrant q +
              totalQuadrant q := by
      intro q
      simpa [completeQuadrant, incompleteQuadrant, swappedQuadrant, totalQuadrant,
        swappedIncompletePointLeft, swappedIncompletePointRight] using
        gHatPairProduct_qSDDOp_decompose params ψbi family q
    rcases hcommComplete.pairwiseCompletePartCommutation with ⟨hcomplete_bound⟩
    rcases hcommIncomplete.pointWithIncompletePartCommutation with ⟨hincomplete_point_bound⟩
    rcases hcommIncomplete.incompletePartCommutation with ⟨hincomplete_total_bound⟩
    refine ⟨?_⟩
    calc
      _root_.LIDT.MIPStarRE.LDT.sddErrorOp ψbi
          (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SlicePairQuestion params))
          (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatPairProductLeft params family)
          (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatPairProductRight params family)
        =
          _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SlicePairQuestion params))
            (fun q =>
              completeQuadrant q +
                incompleteQuadrant q +
                swappedQuadrant q +
                totalQuadrant q) := by
            unfold _root_.LIDT.MIPStarRE.LDT.sddErrorOp
            apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
            exact hdecomp_q
      _ =
          _root_.LIDT.MIPStarRE.LDT.sddErrorOp ψbi
            (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SlicePairQuestion params))
            (fun q =>
              _root_.LIDT.MIPStarRE.LDT.OpFamily.leftPlacedOpFamily (ιB := ι) <|
                _root_.LIDT.MIPStarRE.LDT.CommutativityPoints.orderedProductOpFamily
                  ((family.meas q.1).toSubMeas)
                  ((family.meas q.2).toSubMeas))
            (fun q =>
              _root_.LIDT.MIPStarRE.LDT.OpFamily.leftPlacedOpFamily (ιB := ι) <|
                _root_.LIDT.MIPStarRE.LDT.CommutativityPoints.reversedProductOpFamily
                  ((family.meas q.1).toSubMeas)
                  ((family.meas q.2).toSubMeas)) +
          _root_.LIDT.MIPStarRE.LDT.sddErrorOp ψbi
            (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SlicePairQuestion params))
            (_root_.LIDT.MIPStarRE.LDT.Pasting.incompletePartPointProductLeft params family)
            (_root_.LIDT.MIPStarRE.LDT.Pasting.incompletePartPointProductRight params family) +
          _root_.LIDT.MIPStarRE.LDT.sddErrorOp ψbi
            (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SlicePairQuestion params))
            swappedIncompletePointLeft
            swappedIncompletePointRight +
          _root_.LIDT.MIPStarRE.LDT.sddErrorOp ψbi
            (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SlicePairQuestion params))
            (_root_.LIDT.MIPStarRE.LDT.Pasting.incompletePartTotalProductLeft params family)
            (_root_.LIDT.MIPStarRE.LDT.Pasting.incompletePartTotalProductRight params family) := by
              unfold _root_.LIDT.MIPStarRE.LDT.sddErrorOp
              rw [_root_.LIDT.MIPStarRE.LDT.avgOver_add, _root_.LIDT.MIPStarRE.LDT.avgOver_add, _root_.LIDT.MIPStarRE.LDT.avgOver_add]
      _ ≤
          _root_.LIDT.MIPStarRE.LDT.Pasting.pairwiseCompletePartCommutationError params gamma zeta +
            _root_.LIDT.MIPStarRE.LDT.Pasting.commutingWithGIncompleteError params gamma zeta +
            _root_.LIDT.MIPStarRE.LDT.Pasting.commutingWithGIncompleteError params gamma zeta +
            _root_.LIDT.MIPStarRE.LDT.Pasting.commutingWithGIncompleteError params gamma zeta := by
              gcongr
      _ ≤ _root_.LIDT.MIPStarRE.LDT.Pasting.gHatCommutationError params gamma zeta := by
            set quarterSum : _root_.LIDT.MIPStarRE.LDT.Error :=
              Real.rpow gamma (1 / (4 : _root_.LIDT.MIPStarRE.LDT.Error)) +
                Real.rpow zeta (1 / (4 : _root_.LIDT.MIPStarRE.LDT.Error)) +
                Real.rpow (((params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error))) (1 / (4 : _root_.LIDT.MIPStarRE.LDT.Error))
            set sixteenthSum : _root_.LIDT.MIPStarRE.LDT.Error :=
              Real.rpow gamma (1 / (16 : _root_.LIDT.MIPStarRE.LDT.Error)) +
                Real.rpow zeta (1 / (16 : _root_.LIDT.MIPStarRE.LDT.Error)) +
                Real.rpow (((params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error))) (1 / (16 : _root_.LIDT.MIPStarRE.LDT.Error))
            have hquarter_le :
                quarterSum ≤ sixteenthSum := by
              dsimp [quarterSum, sixteenthSum]
              exact add_le_add (add_le_add hquarter_gamma hquarter_zeta) hquarter_ratio
            have hm_nonneg : 0 ≤ (params.m : _root_.LIDT.MIPStarRE.LDT.Error) := by positivity
            calc
              _root_.LIDT.MIPStarRE.LDT.Pasting.pairwiseCompletePartCommutationError params gamma zeta +
                  _root_.LIDT.MIPStarRE.LDT.Pasting.commutingWithGIncompleteError params gamma zeta +
                  _root_.LIDT.MIPStarRE.LDT.Pasting.commutingWithGIncompleteError params gamma zeta +
                  _root_.LIDT.MIPStarRE.LDT.Pasting.commutingWithGIncompleteError params gamma zeta
                =
                  30 * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * quarterSum +
                    36 * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * sixteenthSum +
                    36 * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * sixteenthSum +
                    36 * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * sixteenthSum := by
                      simp [_root_.LIDT.MIPStarRE.LDT.Pasting.pairwiseCompletePartCommutationError, quarterSum,
                        _root_.LIDT.MIPStarRE.LDT.Pasting.commutingWithGIncompleteError, _root_.LIDT.MIPStarRE.LDT.Pasting.commutingWithGCompleteError,
                        sixteenthSum, _root_.LIDT.MIPStarRE.LDT.Commutativity.comMainError]
              _ ≤
                  30 * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * sixteenthSum +
                    36 * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * sixteenthSum +
                    36 * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * sixteenthSum +
                    36 * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * sixteenthSum := by
                      gcongr
              _ = _root_.LIDT.MIPStarRE.LDT.Pasting.gHatCommutationError params gamma zeta := by
                    simp [_root_.LIDT.MIPStarRE.LDT.Pasting.gHatCommutationError, sixteenthSum]
                    ring
