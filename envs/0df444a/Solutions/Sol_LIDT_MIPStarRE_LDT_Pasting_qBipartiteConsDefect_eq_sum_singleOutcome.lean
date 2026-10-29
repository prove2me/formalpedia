-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Pasting.qBipartiteConsDefect_eq_sum_singleOutcome
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T16:33:32.735452+00:00
-- url     : https://prove2.me/submissions/fd74e335-686a-4d53-b758-dc7fd348618b

-- Generated proof for MIPStarRE.LDT.Pasting.qBipartiteConsDefect_eq_sum_singleOutcome.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LineInterpolation_BadLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LineInterpolation_BadMass
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LineInterpolation_Core
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
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_qBipartiteConsDefect_eq_false_mass_of_bool_right_true

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

/- Source helpers from MIPStarRE/LDT/Pasting/ComparisonLemmas/LineInterpolation/BadMass.lean. -/
/-!
# Line interpolation: bad-mass comparison

Main bad-mass comparison lemmas: sandwich mismatch sums, `qBipartiteConsDefect`
equality via single-outcome measurements, `hBConsistencyBadMass`, line-point
defect bounds, and `pastedInterpolation_verticalLine_defect_le_badMass`.

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











lemma qBipartiteConsDefect_postprocess_eq_singleOutcome
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (ψ : QuantumState (ι × ι))
    (A B : SubMeas Outcome ι) (a0 : Outcome) :
    qBipartiteConsDefect ψ (postprocess A (fun a => decide (a = a0)))
      (singleOutcomeRightSubMeas B a0) =
        ev ψ
          (opTensor ((postprocess A (fun a => decide (a = a0))).outcome false)
            (B.outcome a0)) := by
  refine qBipartiteConsDefect_eq_false_mass_of_bool_right_true ψ
    (postprocess A (fun a => decide (a = a0))) (singleOutcomeRightSubMeas B a0) ?_ ?_
  · rfl
  · rfl

lemma postprocess_decide_eq_true_outcome
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (A : SubMeas Outcome ι) (a0 : Outcome) :
    (postprocess A (fun a => decide (a = a0))).outcome true = A.outcome a0 := by
  simp [postprocess, Finset.sum_filter]

lemma postprocess_decide_false_add_true_eq_total
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (A : SubMeas Outcome ι) (a0 : Outcome) :
    (postprocess A (fun a => decide (a = a0))).outcome false + A.outcome a0 = A.total := by
  set P := postprocess A (fun a => decide (a = a0))
  have hsum : ∑ b : Bool, P.outcome b = P.total := P.sum_eq_total
  have hexpand : ∑ b : Bool, P.outcome b = P.outcome false + P.outcome true := by
    rw [Fintype.sum_bool]
    exact add_comm _ _
  have htotal : P.total = A.total := postprocess_total A _
  have htrue : P.outcome true = A.outcome a0 :=
    postprocess_decide_eq_true_outcome A a0
  rw [hexpand, htrue] at hsum
  rw [htotal] at hsum
  exact hsum























end MIPStarRE.LDT.Pasting

end

end LIDT

open LIDT
/-!
# Line interpolation: bad-mass comparison

Main bad-mass comparison lemmas: sandwich mismatch sums, `qBipartiteConsDefect`
equality via single-outcome measurements, `hBConsistencyBadMass`, line-point
defect bounds, and `pastedInterpolation_verticalLine_defect_le_badMass`.

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
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (ψ : _root_.LIDT.MIPStarRE.LDT.QuantumState (ι × ι))
    (A : _root_.LIDT.MIPStarRE.LDT.SubMeas Outcome ι)
    (B : _root_.LIDT.MIPStarRE.LDT.Measurement Outcome ι) :
    _root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect ψ A B.toSubMeas =
      ∑ a0 : Outcome,
        _root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect ψ (_root_.LIDT.MIPStarRE.LDT.postprocess A (fun a => decide (a = a0)))
          (_root_.LIDT.MIPStarRE.LDT.Pasting.singleOutcomeRightSubMeas B.toSubMeas a0) := by
  have hsingle_term : ∀ a0 : Outcome,
      _root_.LIDT.MIPStarRE.LDT.ev ψ (_root_.LIDT.MIPStarRE.LDT.opTensor A.total (B.outcome a0)) =
        _root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect ψ (_root_.LIDT.MIPStarRE.LDT.postprocess A (fun a => decide (a = a0)))
          (_root_.LIDT.MIPStarRE.LDT.Pasting.singleOutcomeRightSubMeas B.toSubMeas a0) +
          _root_.LIDT.MIPStarRE.LDT.ev ψ (_root_.LIDT.MIPStarRE.LDT.opTensor (A.outcome a0) (B.outcome a0)) := by
    intro a0
    calc
      _root_.LIDT.MIPStarRE.LDT.ev ψ (_root_.LIDT.MIPStarRE.LDT.opTensor A.total (B.outcome a0))
        = _root_.LIDT.MIPStarRE.LDT.ev ψ (_root_.LIDT.MIPStarRE.LDT.opTensor ((_root_.LIDT.MIPStarRE.LDT.postprocess A (fun a => decide (a = a0))).outcome false + A.outcome a0)
            (B.outcome a0)) := by
              rw [_root_.LIDT.MIPStarRE.LDT.Pasting.postprocess_decide_false_add_true_eq_total]
      _ = _root_.LIDT.MIPStarRE.LDT.ev ψ
            (_root_.LIDT.MIPStarRE.LDT.opTensor ((_root_.LIDT.MIPStarRE.LDT.postprocess A (fun a => decide (a = a0))).outcome false) (B.outcome a0) +
              _root_.LIDT.MIPStarRE.LDT.opTensor (A.outcome a0) (B.outcome a0)) := by
              rw [_root_.LIDT.MIPStarRE.LDT.opTensor_add_left_local]
      _ = _root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect ψ (_root_.LIDT.MIPStarRE.LDT.postprocess A (fun a => decide (a = a0)))
            (_root_.LIDT.MIPStarRE.LDT.Pasting.singleOutcomeRightSubMeas B.toSubMeas a0) +
          _root_.LIDT.MIPStarRE.LDT.ev ψ (_root_.LIDT.MIPStarRE.LDT.opTensor (A.outcome a0) (B.outcome a0)) := by
            rw [_root_.LIDT.MIPStarRE.LDT.ev_add, _root_.LIDT.MIPStarRE.LDT.Pasting.qBipartiteConsDefect_postprocess_eq_singleOutcome]
  have htotal_sum :
      _root_.LIDT.MIPStarRE.LDT.ev ψ (_root_.LIDT.MIPStarRE.LDT.opTensor A.total B.toSubMeas.total) =
        ∑ a0 : Outcome, _root_.LIDT.MIPStarRE.LDT.ev ψ (_root_.LIDT.MIPStarRE.LDT.opTensor A.total (B.outcome a0)) := by
    rw [← B.sum_eq_total]
    rw [_root_.LIDT.MIPStarRE.LDT.opTensor_sum_right_finset, _root_.LIDT.MIPStarRE.LDT.ev_finset_sum]
  have hdecomp :
      _root_.LIDT.MIPStarRE.LDT.ev ψ (_root_.LIDT.MIPStarRE.LDT.opTensor A.total B.toSubMeas.total) - _root_.LIDT.MIPStarRE.LDT.qBipartiteMatchMass ψ A B.toSubMeas =
        ∑ a0 : Outcome,
          _root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect ψ (_root_.LIDT.MIPStarRE.LDT.postprocess A (fun a => decide (a = a0)))
            (_root_.LIDT.MIPStarRE.LDT.Pasting.singleOutcomeRightSubMeas B.toSubMeas a0) := by
    rw [htotal_sum, _root_.LIDT.MIPStarRE.LDT.qBipartiteMatchMass]
    calc
      ∑ a0 : Outcome, _root_.LIDT.MIPStarRE.LDT.ev ψ (_root_.LIDT.MIPStarRE.LDT.opTensor A.total (B.outcome a0)) -
          ∑ a : Outcome, _root_.LIDT.MIPStarRE.LDT.ev ψ (_root_.LIDT.MIPStarRE.LDT.opTensor (A.outcome a) (B.outcome a))
        = (∑ a0 : Outcome,
            (_root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect ψ (_root_.LIDT.MIPStarRE.LDT.postprocess A (fun a => decide (a = a0)))
              (_root_.LIDT.MIPStarRE.LDT.Pasting.singleOutcomeRightSubMeas B.toSubMeas a0) +
              _root_.LIDT.MIPStarRE.LDT.ev ψ (_root_.LIDT.MIPStarRE.LDT.opTensor (A.outcome a0) (B.outcome a0)))) -
            ∑ a : Outcome, _root_.LIDT.MIPStarRE.LDT.ev ψ (_root_.LIDT.MIPStarRE.LDT.opTensor (A.outcome a) (B.outcome a)) := by
              refine congrArg (fun t => t - ∑ a : Outcome,
                  _root_.LIDT.MIPStarRE.LDT.ev ψ (_root_.LIDT.MIPStarRE.LDT.opTensor (A.outcome a) (B.outcome a))) ?_
              exact Finset.sum_congr rfl fun a _ => hsingle_term a
      _ = ∑ a0 : Outcome,
            _root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect ψ (_root_.LIDT.MIPStarRE.LDT.postprocess A (fun a => decide (a = a0)))
              (_root_.LIDT.MIPStarRE.LDT.Pasting.singleOutcomeRightSubMeas B.toSubMeas a0) := by
            rw [Finset.sum_add_distrib]
            ring
  have hnonneg :
      0 ≤ ∑ a0 : Outcome,
        _root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect ψ (_root_.LIDT.MIPStarRE.LDT.postprocess A (fun a => decide (a = a0)))
          (_root_.LIDT.MIPStarRE.LDT.Pasting.singleOutcomeRightSubMeas B.toSubMeas a0) := by
    exact Finset.sum_nonneg fun a0 _ =>
      _root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect_nonneg ψ _ _
  rw [_root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect, hdecomp, max_eq_right hnonneg]
