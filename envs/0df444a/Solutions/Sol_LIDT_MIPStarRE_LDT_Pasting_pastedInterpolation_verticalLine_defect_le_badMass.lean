-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Pasting.pastedInterpolation_verticalLine_defect_le_badMass
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T16:55:34.615128+00:00
-- url     : https://prove2.me/submissions/ef9ca1de-1a8f-4729-bc21-2e21c909e465

-- Generated proof for MIPStarRE.LDT.Pasting.pastedInterpolation_verticalLine_defect_le_badMass.
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
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_qBipartiteConsDefect_eq_sum_singleOutcome
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_tupleInterpolatedVerticalLine_ne_gives_exists_some_eval_mismatch

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

/- Source helpers from MIPStarRE/LDT/Pasting/ComparisonLemmas/Common.lean. -/
/-!
# Section 12 pasting: comparison common helpers

Shared postprocessing, symmetry, distribution, boundedness, and arithmetic helpers for the Section
12 comparison lemmas.

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

lemma postprocess_postprocess
    {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (A : SubMeas α ι) (f : α → β) (g : β → γ) :
    postprocess (postprocess A f) g = postprocess A (g ∘ f) := by
  classical
  refine SubMeas.ext ?_ ?_
  · intro c
    simp [postprocess, Function.comp, Finset.sum_filter, Finset.sum_comm, eq_comm]
  · simp [postprocess_total]





















end MIPStarRE.LDT.Pasting

end

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

lemma interpolationEligibleSandwich_mismatch_sum_mono
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    {k : ℕ}
    (u : Point params)
    (xs : PointTuple params k)
    (hxs : Function.Injective xs)
    (f : AxisLinePolynomial params.next) :
    ∑ gs : GHatTupleOutcome params k,
        (if IsGloballyConsistent params xs gs
            ∧ tupleInterpolatedVerticalLine params u xs gs ≠ f then
          (interpolationEligibleSandwichFamily params family k xs).outcome gs
        else 0)
      ≤
      ∑ gs : GHatTupleOutcome params k,
        (if ∃ i : Fin k, ∃ hiSome : (gs i).isSome = true,
            ((gs i).get hiSome) u ≠ f (xs i) then
          (interpolationEligibleSandwichFamily params family k xs).outcome gs
        else 0) := by
  refine Finset.sum_le_sum ?_
  intro gs _
  by_cases hglob : IsGloballyConsistent params xs gs
  · by_cases hneq : tupleInterpolatedVerticalLine params u xs gs ≠ f
    · by_cases hEligible : InterpolationEligible params gs
      · rcases tupleInterpolatedVerticalLine_ne_gives_exists_some_eval_mismatch
          params u xs hxs gs hEligible hglob f hneq with ⟨i, hiSome, hm⟩
        have hright :
            ∃ i : Fin k, ∃ hiSome : (gs i).isSome = true, ((gs i).get hiSome) u ≠ f (xs i) :=
          ⟨i, hiSome, hm⟩
        simp [hglob, hneq, hright]
      · simp [interpolationEligibleSandwichFamily, restrictSubMeas, hEligible, hglob, hneq]
    · by_cases hright : ∃ i : Fin k, ∃ hiSome : (gs i).isSome = true,
        ((gs i).get hiSome) u ≠ f (xs i)
      · have hnonneg : 0 ≤ (interpolationEligibleSandwichFamily params family k xs).outcome gs :=
          (interpolationEligibleSandwichFamily params family k xs).outcome_pos gs
        simp [hglob, hneq, hright, hnonneg]
      · simp [hglob, hneq, hright]
  · by_cases hright : ∃ i : Fin k, ∃ hiSome : (gs i).isSome = true, ((gs i).get hiSome) u ≠ f (xs i)
    · have hnonneg : 0 ≤ (interpolationEligibleSandwichFamily params family k xs).outcome gs :=
        (interpolationEligibleSandwichFamily params family k xs).outcome_pos gs
      simp [hglob, hright, hnonneg]
    · simp [hglob, hright]



lemma pastedInterpolation_verticalLine_singleOutcome_postprocess
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (k : ℕ)
    (u : Point params)
    (xs : PointTuple params k)
    (f : AxisLinePolynomial params.next) :
    postprocess
      (hRestrictionToVerticalLine params (pastedInterpolationFamily params family k xs) u)
      (fun h => decide (h = f)) =
    postprocess
      (restrictSubMeas (interpolationEligibleSandwichFamily params family k xs)
        (IsGloballyConsistent params xs))
      (fun gs => decide (tupleInterpolatedVerticalLine params u xs gs = f)) := by
  rw [pastedInterpolationFamily, hRestrictionToVerticalLine]
  rw [postprocess_postprocess, postprocess_postprocess]
  congr 1





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























lemma postprocess_restrictSubMeas_outcome
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (A : SubMeas α ι) (p : α → Prop) [DecidablePred p]
    (f : α → β) (b : β) :
    (postprocess (restrictSubMeas A p) f).outcome b =
      ∑ a : α, if p a ∧ f a = b then A.outcome a else 0 := by
  classical
  ext i j
  simp only [postprocess, restrictSubMeas, Matrix.sum_apply, Finset.sum_filter]
  refine Finset.sum_congr rfl ?_
  intro c _
  by_cases hf : f c = b <;> by_cases hp : p c <;>
    simp [hf, hp]



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
    (params : _root_.LIDT.MIPStarRE.LDT.Parameters) [_root_.LIDT.MIPStarRE.LDT.FieldModel params.q]
    (strategy : _root_.LIDT.MIPStarRE.LDT.SymStrat params.next ι)
    (family : _root_.LIDT.MIPStarRE.LDT.IdxPolyFamily params ι)
    {k : ℕ}
    (u : _root_.LIDT.MIPStarRE.LDT.Point params)
    (xs : _root_.LIDT.MIPStarRE.LDT.PointTuple params k)
    (hxs : Function.Injective xs) :
    _root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect strategy.state
      (_root_.LIDT.MIPStarRE.LDT.Pasting.hRestrictionToVerticalLine params (_root_.LIDT.MIPStarRE.LDT.Pasting.pastedInterpolationFamily params family k xs) u)
      (_root_.LIDT.MIPStarRE.LDT.Pasting.verticalLineMeasurementFamily params strategy u)
      ≤ _root_.LIDT.MIPStarRE.LDT.Pasting.hBConsistencyBadMass params strategy family u xs := by
  let ℓ : _root_.LIDT.MIPStarRE.LDT.AxisParallelLine params.next :=
    { base := _root_.LIDT.MIPStarRE.LDT.appendPoint params u _root_.LIDT.MIPStarRE.LDT.zeroCoord
      direction := _root_.LIDT.MIPStarRE.LDT.lastCoord params }
  let Bm : _root_.LIDT.MIPStarRE.LDT.Measurement (_root_.LIDT.MIPStarRE.LDT.AxisLinePolynomial params.next) ι :=
    (strategy.axisParallelMeasurement ℓ).toMeasurement
  have hB : Bm.toSubMeas = _root_.LIDT.MIPStarRE.LDT.Pasting.verticalLineMeasurementFamily params strategy u := by
    simp [Bm, ℓ, _root_.LIDT.MIPStarRE.LDT.Pasting.verticalLineMeasurementFamily]
  rw [← hB, _root_.LIDT.MIPStarRE.LDT.Pasting.qBipartiteConsDefect_eq_sum_singleOutcome (B := Bm)]
  exact Finset.sum_le_sum (fun f _ => by
    calc
      _root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect strategy.state
          (_root_.LIDT.MIPStarRE.LDT.postprocess (_root_.LIDT.MIPStarRE.LDT.Pasting.hRestrictionToVerticalLine params (
              _root_.LIDT.MIPStarRE.LDT.Pasting.pastedInterpolationFamily params family k xs) u)
            (fun h => decide (h = f)))
          (_root_.LIDT.MIPStarRE.LDT.Pasting.singleOutcomeRightSubMeas Bm.toSubMeas f)
        = _root_.LIDT.MIPStarRE.LDT.ev strategy.state
            (_root_.LIDT.MIPStarRE.LDT.opTensor
              ((_root_.LIDT.MIPStarRE.LDT.postprocess (_root_.LIDT.MIPStarRE.LDT.Pasting.hRestrictionToVerticalLine params (
                  _root_.LIDT.MIPStarRE.LDT.Pasting.pastedInterpolationFamily params family k xs) u)
                (fun h => decide (h = f))).outcome false)
              (Bm.outcome f)) := by
                rw [_root_.LIDT.MIPStarRE.LDT.Pasting.qBipartiteConsDefect_postprocess_eq_singleOutcome]
      _ = _root_.LIDT.MIPStarRE.LDT.ev strategy.state
            (_root_.LIDT.MIPStarRE.LDT.opTensor
              (∑ gs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params k,
                if _root_.LIDT.MIPStarRE.LDT.Pasting.IsGloballyConsistent params xs gs
                    ∧ _root_.LIDT.MIPStarRE.LDT.Pasting.tupleInterpolatedVerticalLine params u xs gs ≠ f then
                  (_root_.LIDT.MIPStarRE.LDT.Pasting.interpolationEligibleSandwichFamily params family k xs).outcome gs
                else 0)
              (Bm.outcome f)) := by
                rw [_root_.LIDT.MIPStarRE.LDT.Pasting.pastedInterpolation_verticalLine_singleOutcome_postprocess,
                  _root_.LIDT.MIPStarRE.LDT.Pasting.postprocess_restrictSubMeas_outcome]
                simp [decide_eq_false_iff_not]
      _ ≤ _root_.LIDT.MIPStarRE.LDT.ev strategy.state
            (_root_.LIDT.MIPStarRE.LDT.opTensor
              (∑ gs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params k,
                if ∃ i : Fin k, ∃ hiSome : (gs i).isSome = true,
                    ((gs i).get hiSome) u ≠ f (xs i) then
                  (_root_.LIDT.MIPStarRE.LDT.Pasting.interpolationEligibleSandwichFamily params family k xs).outcome gs
                else 0)
              (Bm.outcome f)) := by
                apply _root_.LIDT.MIPStarRE.LDT.ev_mono strategy.state _ _
                exact _root_.LIDT.MIPStarRE.LDT.opTensor_mono_left
                  (_root_.LIDT.MIPStarRE.LDT.Pasting.interpolationEligibleSandwich_mismatch_sum_mono params family u xs hxs f)
                  (Bm.outcome_pos f)
      _ = _root_.LIDT.MIPStarRE.LDT.ev strategy.state
            (_root_.LIDT.MIPStarRE.LDT.opTensor
              (∑ gs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params k,
                if ∃ i : Fin k, ∃ hiSome : (gs i).isSome = true,
                    ((gs i).get hiSome) u ≠ f (xs i) then
                  (_root_.LIDT.MIPStarRE.LDT.Pasting.interpolationEligibleSandwichFamily params family k xs).outcome gs
                else 0)
              ((_root_.LIDT.MIPStarRE.LDT.Pasting.verticalLineMeasurementFamily params strategy u).outcome f)) := by
                simp [hB])
