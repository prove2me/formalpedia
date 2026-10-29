-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Pasting.commutingWithGIncomplete_ofComplete
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T16:01:56.534296+00:00
-- url     : https://prove2.me/submissions/f34c0032-f0b2-419b-b822-48ccf097dccd

-- Generated proof for MIPStarRE.LDT.Pasting.commutingWithGIncomplete_ofComplete.
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
# Section 12 pasting: commuting-with-G incomplete part

Incomplete-part commuting-with-`G` bounds.
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
    (hcomm : _root_.LIDT.MIPStarRE.LDT.Pasting.CommutingWithGCompleteStatement params ψbi family gamma zeta) :
    _root_.LIDT.MIPStarRE.LDT.Pasting.CommutingWithGIncompleteStatement params ψbi family gamma zeta := by
  refine {
    pointWithIncompletePartCommutation := ?_
    incompletePartCommutation := ?_
  }
  · rcases hcomm.pointWithCompletePartCommutation with ⟨hcomplete_bound⟩
    refine ⟨?_⟩
    calc
      _root_.LIDT.MIPStarRE.LDT.sddErrorOp ψbi
          (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SlicePairQuestion params))
          (_root_.LIDT.MIPStarRE.LDT.Pasting.incompletePartPointProductLeft params family)
          (_root_.LIDT.MIPStarRE.LDT.Pasting.incompletePartPointProductRight params family)
        =
          _root_.LIDT.MIPStarRE.LDT.sddErrorOp ψbi
            (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SlicePairQuestion params))
            (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartPointProductLeft params family)
            (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartPointProductRight params family) := by
              unfold _root_.LIDT.MIPStarRE.LDT.sddErrorOp
              apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
              intro q
              unfold _root_.LIDT.MIPStarRE.LDT.qSDDOp _root_.LIDT.MIPStarRE.LDT.qSDDCore
              apply Finset.sum_congr rfl
              intro g _hg
              have hdiff :
                  (_root_.LIDT.MIPStarRE.LDT.Pasting.incompletePartPointProductLeft params family q).outcome g -
                      (_root_.LIDT.MIPStarRE.LDT.Pasting.incompletePartPointProductRight params family q).outcome g =
                    -((_root_.LIDT.MIPStarRE.LDT.Pasting.completePartPointProductLeft params family q).outcome g -
                      (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartPointProductRight params family q).outcome g) := by
                let A : _root_.LIDT.MIPStarRE.Quantum.Op ι := (family.meas q.1).outcome g
                let B : _root_.LIDT.MIPStarRE.Quantum.Op ι :=
                  (_root_.LIDT.MIPStarRE.LDT.postprocess ((family.meas q.2).toSubMeas) (fun _ => ())).total
                have hinner : A * (1 - B) - (1 - B) * A = -(A * B - B * A) := by
                  dsimp [A, B]
                  noncomm_ring
                ext i j
                rcases i with ⟨i₁, i₂⟩
                rcases j with ⟨j₁, j₂⟩
                by_cases h₂ : i₂ = j₂
                · have hentry := congrArg (fun X : _root_.LIDT.MIPStarRE.Quantum.Op ι => X i₁ j₁) hinner
                  simpa [_root_.LIDT.MIPStarRE.LDT.Pasting.incompletePartPointProductLeft, _root_.LIDT.MIPStarRE.LDT.Pasting.incompletePartPointProductRight,
                    _root_.LIDT.MIPStarRE.LDT.Pasting.completePartPointProductLeft, _root_.LIDT.MIPStarRE.LDT.Pasting.completePartPointProductRight,
                    _root_.LIDT.MIPStarRE.LDT.OpFamily.leftPlacedOpFamily, _root_.LIDT.MIPStarRE.LDT.Pasting.multiplyByTotalOnRight,
                    _root_.LIDT.MIPStarRE.LDT.Pasting.multiplyByTotalOnLeft, _root_.LIDT.MIPStarRE.LDT.Pasting.incompletePartSubMeas, _root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas,
                    sub_eq_add_neg, _root_.LIDT.MIPStarRE.LDT.leftTensor, A, B, h₂] using hentry
                · simp [_root_.LIDT.MIPStarRE.LDT.Pasting.incompletePartPointProductLeft, _root_.LIDT.MIPStarRE.LDT.Pasting.incompletePartPointProductRight,
                    _root_.LIDT.MIPStarRE.LDT.Pasting.completePartPointProductLeft, _root_.LIDT.MIPStarRE.LDT.Pasting.completePartPointProductRight,
                    _root_.LIDT.MIPStarRE.LDT.OpFamily.leftPlacedOpFamily, _root_.LIDT.MIPStarRE.LDT.Pasting.multiplyByTotalOnRight,
                    _root_.LIDT.MIPStarRE.LDT.Pasting.multiplyByTotalOnLeft, _root_.LIDT.MIPStarRE.LDT.Pasting.incompletePartSubMeas, _root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas,
                    sub_eq_add_neg, _root_.LIDT.MIPStarRE.LDT.leftTensor, h₂]
              rw [hdiff]
              have hswap :
                  (((_root_.LIDT.MIPStarRE.LDT.Pasting.completePartPointProductRight params family q).outcome g)ᴴ -
                        ((_root_.LIDT.MIPStarRE.LDT.Pasting.completePartPointProductLeft params family q).outcome g)ᴴ) *
                      ((_root_.LIDT.MIPStarRE.LDT.Pasting.completePartPointProductRight params family q).outcome g -
                        (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartPointProductLeft params family q).outcome g) =
                    (((_root_.LIDT.MIPStarRE.LDT.Pasting.completePartPointProductLeft params family q).outcome g)ᴴ -
                        ((_root_.LIDT.MIPStarRE.LDT.Pasting.completePartPointProductRight params family q).outcome g)ᴴ) *
                      ((_root_.LIDT.MIPStarRE.LDT.Pasting.completePartPointProductLeft params family q).outcome g -
                        (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartPointProductRight params family q).outcome g) := by
                noncomm_ring
              simpa [sub_eq_add_neg] using congrArg (_root_.LIDT.MIPStarRE.LDT.ev ψbi) hswap
      _ ≤ _root_.LIDT.MIPStarRE.LDT.Pasting.commutingWithGIncompleteError params gamma zeta := by
          simpa [_root_.LIDT.MIPStarRE.LDT.Pasting.commutingWithGIncompleteError] using hcomplete_bound
  · rcases hcomm.completePartCommutation with ⟨hcomplete_bound⟩
    refine ⟨?_⟩
    calc
      _root_.LIDT.MIPStarRE.LDT.sddErrorOp ψbi
          (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SlicePairQuestion params))
          (_root_.LIDT.MIPStarRE.LDT.Pasting.incompletePartTotalProductLeft params family)
          (_root_.LIDT.MIPStarRE.LDT.Pasting.incompletePartTotalProductRight params family)
        =
          _root_.LIDT.MIPStarRE.LDT.sddErrorOp ψbi
            (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SlicePairQuestion params))
            (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartTotalProductLeft params family)
            (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartTotalProductRight params family) := by
              unfold _root_.LIDT.MIPStarRE.LDT.sddErrorOp
              apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
              intro q
              unfold _root_.LIDT.MIPStarRE.LDT.qSDDOp _root_.LIDT.MIPStarRE.LDT.qSDDCore
              apply Finset.sum_congr rfl
              intro u _hu
              cases u
              have hq1 :
                  (_root_.LIDT.MIPStarRE.LDT.postprocess ((family.meas q.1).toSubMeas) (fun _ => ())).outcome () =
                    (family.meas q.1).total := by
                calc
                  (_root_.LIDT.MIPStarRE.LDT.postprocess ((family.meas q.1).toSubMeas) (fun _ => ())).outcome () =
                      (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family q.1).total := by
                    exact _root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas_outcome_unit
                      (params := params) (family := family) q.1
                  _ = (family.meas q.1).total := by
                    exact _root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas_total
                      (params := params) (family := family) q.1
              have hq2 :
                  (_root_.LIDT.MIPStarRE.LDT.postprocess ((family.meas q.2).toSubMeas) (fun _ => ())).outcome () =
                    (family.meas q.2).total := by
                calc
                  (_root_.LIDT.MIPStarRE.LDT.postprocess ((family.meas q.2).toSubMeas) (fun _ => ())).outcome () =
                      (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family q.2).total := by
                    exact _root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas_outcome_unit
                      (params := params) (family := family) q.2
                  _ = (family.meas q.2).total := by
                    exact _root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas_total
                      (params := params) (family := family) q.2
              have hdiff :
                  (_root_.LIDT.MIPStarRE.LDT.Pasting.incompletePartTotalProductLeft params family q).outcome () -
                      (_root_.LIDT.MIPStarRE.LDT.Pasting.incompletePartTotalProductRight params family q).outcome () =
                    (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartTotalProductLeft params family q).outcome () -
                      (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartTotalProductRight params family q).outcome () := by
                let A : _root_.LIDT.MIPStarRE.Quantum.Op ι :=
                  (_root_.LIDT.MIPStarRE.LDT.postprocess ((family.meas q.1).toSubMeas) (fun _ => ())).total
                let B : _root_.LIDT.MIPStarRE.Quantum.Op ι :=
                  (_root_.LIDT.MIPStarRE.LDT.postprocess ((family.meas q.2).toSubMeas) (fun _ => ())).total
                have hinner : (1 - A) * (1 - B) - (1 - B) * (1 - A) = A * B - B * A := by
                  dsimp [A, B]
                  noncomm_ring
                have hA : A = (family.meas q.1).total := by
                  dsimp [A]
                  exact _root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas_total
                    (params := params) (family := family) q.1
                have hB : B = (family.meas q.2).total := by
                  dsimp [B]
                  exact _root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas_total
                    (params := params) (family := family) q.2
                ext i j
                rcases i with ⟨i₁, i₂⟩
                rcases j with ⟨j₁, j₂⟩
                by_cases h₂ : i₂ = j₂
                · have hentry := congrArg (fun X : _root_.LIDT.MIPStarRE.Quantum.Op ι => X i₁ j₁) hinner
                  simpa [_root_.LIDT.MIPStarRE.LDT.Pasting.incompletePartTotalProductLeft, _root_.LIDT.MIPStarRE.LDT.Pasting.incompletePartTotalProductRight,
                    _root_.LIDT.MIPStarRE.LDT.Pasting.completePartTotalProductLeft, _root_.LIDT.MIPStarRE.LDT.Pasting.completePartTotalProductRight,
                    _root_.LIDT.MIPStarRE.LDT.OpFamily.leftPlacedOpFamily, _root_.LIDT.MIPStarRE.LDT.Pasting.multiplyByTotalOnRight,
                    _root_.LIDT.MIPStarRE.LDT.Pasting.multiplyByTotalOnLeft, _root_.LIDT.MIPStarRE.LDT.Pasting.incompletePartSubMeas, _root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas,
                    sub_eq_add_neg, _root_.LIDT.MIPStarRE.LDT.leftTensor, A, B, hA, hB, hq1, hq2, h₂,
                    (family.meas q.1).sum_eq_total,
                    (family.meas q.2).sum_eq_total] using hentry
                · simp [_root_.LIDT.MIPStarRE.LDT.Pasting.incompletePartTotalProductLeft, _root_.LIDT.MIPStarRE.LDT.Pasting.incompletePartTotalProductRight,
                    _root_.LIDT.MIPStarRE.LDT.Pasting.completePartTotalProductLeft, _root_.LIDT.MIPStarRE.LDT.Pasting.completePartTotalProductRight,
                    _root_.LIDT.MIPStarRE.LDT.OpFamily.leftPlacedOpFamily, _root_.LIDT.MIPStarRE.LDT.Pasting.multiplyByTotalOnRight,
                    _root_.LIDT.MIPStarRE.LDT.Pasting.multiplyByTotalOnLeft, _root_.LIDT.MIPStarRE.LDT.Pasting.incompletePartSubMeas, _root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas,
                    sub_eq_add_neg, _root_.LIDT.MIPStarRE.LDT.leftTensor, h₂, (family.meas q.1).sum_eq_total]
              rw [hdiff]
      _ ≤ _root_.LIDT.MIPStarRE.LDT.Pasting.commutingWithGIncompleteError params gamma zeta := by
          simpa [_root_.LIDT.MIPStarRE.LDT.Pasting.commutingWithGIncompleteError] using hcomplete_bound
