-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Pasting.hBConsistencyCoordMass_le_linePointDefect
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T16:40:01.425227+00:00
-- url     : https://prove2.me/submissions/2b3973de-cdb0-4b06-8fb4-7953032a7b24

-- Generated proof for MIPStarRE.LDT.Pasting.hBConsistencyCoordMass_le_linePointDefect.
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











lemma ldSandwichLineOnePointRightMeasurement_outcome_some_eq_sum
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k : ℕ} (i : Fin k) (q : SandwichedLineQuestion params k) (a : Fq params) :
    (ldSandwichLineOnePointRightMeasurement params strategy family i q).outcome (some a) =
      ∑ f : AxisLinePolynomial params.next,
        if f (q.2 i) = a then
          (verticalLineMeasurementFamily params strategy q.1).outcome f
        else 0 := by
  simp [ldSandwichLineOnePointRightMeasurement, ldSandwichLineOnePointRightFamily,
    postprocess, i.2, Finset.sum_filter]

lemma grouped_coordinate_mismatch_le_left_falseOutcome
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k : ℕ} (u : Point params) (xs : PointTuple params k)
    (i : Fin k) (a : Fq params) :
    (∑ gs : GHatTupleOutcome params k,
      if ∃ hiSome : (gs i).isSome = true, ((gs i).get hiSome) u ≠ a then
        (interpolationEligibleSandwichFamily params family k xs).outcome gs
      else 0)
    ≤
    (postprocess
      ((ldSandwichLineOnePointLeftFamily params strategy family k i.1) (u, xs))
      (fun o => decide (o = some a))).outcome false := by
  have hrewrite :
      (postprocess
        ((ldSandwichLineOnePointLeftFamily params strategy family k i.1) (u, xs))
        (fun o => decide (o = some a))).outcome false =
        ∑ gs : GHatTupleOutcome params k,
          if Option.map (fun g : Polynomial params => g u) (gs i) ≠ some a then
            (restrictSubMeas (gHatSandwichFamily params family k xs)
              (fun gs => (gs i).isSome = true)).outcome gs
          else 0 := by
    rw [ldSandwichLineOnePointLeftFamily, postprocess_postprocess]
    simp [postprocess, Function.comp, i.2, Finset.sum_filter]
  rw [hrewrite]
  refine Finset.sum_le_sum ?_
  intro gs _
  by_cases hm : ∃ hiSome : (gs i).isSome = true, ((gs i).get hiSome) u ≠ a
  · rcases hm with ⟨hiSome, hne⟩
    have hneq : Option.map (fun g : Polynomial params => g u) (gs i) ≠ some a := by
      cases hgi : gs i with
      | none =>
          simp [Option.isSome, hgi] at hiSome
      | some g =>
          simp [hgi] at hiSome
          simpa [hgi] using hne
    by_cases hEligible : InterpolationEligible params gs
    · simp [interpolationEligibleSandwichFamily, restrictSubMeas, hiSome, hneq, hEligible,
        hne]
    · have hnonneg : 0 ≤ (gHatSandwichFamily params family k xs).outcome gs :=
        (gHatSandwichFamily params family k xs).outcome_pos gs
      simp [interpolationEligibleSandwichFamily, restrictSubMeas, hiSome, hneq,
        hEligible, hnonneg]
  · by_cases hneq : Option.map (fun g : Polynomial params => g u) (gs i) ≠ some a
    · have hnonneg :
          0 ≤ (restrictSubMeas (gHatSandwichFamily params family k xs)
            (fun gs => (gs i).isSome = true)).outcome gs :=
        (restrictSubMeas (gHatSandwichFamily params family k xs)
          (fun gs => (gs i).isSome = true)).outcome_pos gs
      simp [hm, hneq, hnonneg]
    · simp [hm, hneq]













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
    {k : ℕ} (u : _root_.LIDT.MIPStarRE.LDT.Point params) (xs : _root_.LIDT.MIPStarRE.LDT.PointTuple params k)
    (i : Fin k) :
    (∑ f : _root_.LIDT.MIPStarRE.LDT.AxisLinePolynomial params.next,
      _root_.LIDT.MIPStarRE.LDT.ev strategy.state
        (_root_.LIDT.MIPStarRE.LDT.opTensor
          (∑ gs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params k,
            if ∃ hiSome : (gs i).isSome = true, ((gs i).get hiSome) u ≠ f (xs i) then
              (_root_.LIDT.MIPStarRE.LDT.Pasting.interpolationEligibleSandwichFamily params family k xs).outcome gs
            else 0)
          ((_root_.LIDT.MIPStarRE.LDT.Pasting.verticalLineMeasurementFamily params strategy u).outcome f)))
      ≤ _root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect strategy.state
          ((_root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointLeftFamily params strategy family k i.1) (u, xs))
          ((_root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointRightFamily params strategy family k i.1) (u, xs)) := by
  let q : _root_.LIDT.MIPStarRE.LDT.Pasting.SandwichedLineQuestion params k := (u, xs)
  let A := ((_root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointLeftFamily params strategy family k i.1) q)
  let Bm := _root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointRightMeasurement params strategy family i q
  let leftFalse : _root_.LIDT.MIPStarRE.LDT.Fq params → _root_.LIDT.MIPStarRE.Quantum.Op ι := fun a =>
    (_root_.LIDT.MIPStarRE.LDT.postprocess A (fun o => decide (o = some a))).outcome false
  have hstep :
      ∀ f : _root_.LIDT.MIPStarRE.LDT.AxisLinePolynomial params.next,
        _root_.LIDT.MIPStarRE.LDT.ev strategy.state
          (_root_.LIDT.MIPStarRE.LDT.opTensor
            (∑ gs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params k,
              if ∃ hiSome : (gs i).isSome = true, ((gs i).get hiSome) u ≠ f (xs i) then
                (_root_.LIDT.MIPStarRE.LDT.Pasting.interpolationEligibleSandwichFamily params family k xs).outcome gs
              else 0)
            ((_root_.LIDT.MIPStarRE.LDT.Pasting.verticalLineMeasurementFamily params strategy u).outcome f))
          ≤ _root_.LIDT.MIPStarRE.LDT.ev strategy.state
              (_root_.LIDT.MIPStarRE.LDT.opTensor (leftFalse (f (xs i)))
                ((_root_.LIDT.MIPStarRE.LDT.Pasting.verticalLineMeasurementFamily params strategy u).outcome f)) := by
    intro f
    exact _root_.LIDT.MIPStarRE.LDT.ev_mono strategy.state _ _ <|
      _root_.LIDT.MIPStarRE.LDT.opTensor_mono_left
        (_root_.LIDT.MIPStarRE.LDT.Pasting.grouped_coordinate_mismatch_le_left_falseOutcome params strategy family u xs i (f (xs i)))
        ((_root_.LIDT.MIPStarRE.LDT.Pasting.verticalLineMeasurementFamily params strategy u).outcome_pos f)
  have hgrouped :
      (∑ f : _root_.LIDT.MIPStarRE.LDT.AxisLinePolynomial params.next,
        _root_.LIDT.MIPStarRE.LDT.ev strategy.state
          (_root_.LIDT.MIPStarRE.LDT.opTensor (leftFalse (f (xs i)))
            ((_root_.LIDT.MIPStarRE.LDT.Pasting.verticalLineMeasurementFamily params strategy u).outcome f)))
        = ∑ a : _root_.LIDT.MIPStarRE.LDT.Fq params,
            _root_.LIDT.MIPStarRE.LDT.ev strategy.state
              (_root_.LIDT.MIPStarRE.LDT.opTensor (leftFalse a) (Bm.outcome (some a))) := by
    calc
      (∑ f : _root_.LIDT.MIPStarRE.LDT.AxisLinePolynomial params.next,
        _root_.LIDT.MIPStarRE.LDT.ev strategy.state
          (_root_.LIDT.MIPStarRE.LDT.opTensor (leftFalse (f (xs i)))
            ((_root_.LIDT.MIPStarRE.LDT.Pasting.verticalLineMeasurementFamily params strategy u).outcome f)))
        = ∑ f : _root_.LIDT.MIPStarRE.LDT.AxisLinePolynomial params.next,
            ∑ a : _root_.LIDT.MIPStarRE.LDT.Fq params,
              if f (xs i) = a then
                _root_.LIDT.MIPStarRE.LDT.ev strategy.state
                  (_root_.LIDT.MIPStarRE.LDT.opTensor (leftFalse a) (
                    (_root_.LIDT.MIPStarRE.LDT.Pasting.verticalLineMeasurementFamily params strategy u).outcome f))
              else (0 : _root_.LIDT.MIPStarRE.LDT.Error) := by
              refine Finset.sum_congr rfl ?_
              intro f _
              have hsingle :
                  (∑ a : _root_.LIDT.MIPStarRE.LDT.Fq params,
                    if f (xs i) = a then
                      _root_.LIDT.MIPStarRE.LDT.ev strategy.state
                        (_root_.LIDT.MIPStarRE.LDT.opTensor (leftFalse a) (
                          (_root_.LIDT.MIPStarRE.LDT.Pasting.verticalLineMeasurementFamily params strategy u).outcome f))
                    else (0 : _root_.LIDT.MIPStarRE.LDT.Error)) =
                  _root_.LIDT.MIPStarRE.LDT.ev strategy.state
                    (_root_.LIDT.MIPStarRE.LDT.opTensor (leftFalse (f (xs i))) (
                      (_root_.LIDT.MIPStarRE.LDT.Pasting.verticalLineMeasurementFamily params strategy u).outcome f)) := by
                let term : _root_.LIDT.MIPStarRE.LDT.Fq params → _root_.LIDT.MIPStarRE.LDT.Error := fun a =>
                  if f (xs i) = a then
                    _root_.LIDT.MIPStarRE.LDT.ev strategy.state
                      (_root_.LIDT.MIPStarRE.LDT.opTensor (leftFalse a) (
                        (_root_.LIDT.MIPStarRE.LDT.Pasting.verticalLineMeasurementFamily params strategy u).outcome f))
                  else 0
                have hsingle :
                    (∑ a ∈ (Finset.univ : Finset (_root_.LIDT.MIPStarRE.LDT.Fq params)), term a) =
                      term (f (xs i)) := by
                  refine Finset.sum_eq_single (f (xs i)) ?_ ?_
                  · intro b _hb hb
                    have hneq : ¬f (xs i) = b := by
                      intro h
                      exact hb h.symm
                    simp [term, hneq]
                  · intro hmem
                    exact False.elim (hmem (Finset.mem_univ _))
                simp
              exact hsingle.symm
      _ = ∑ a : _root_.LIDT.MIPStarRE.LDT.Fq params,
            ∑ f : _root_.LIDT.MIPStarRE.LDT.AxisLinePolynomial params.next,
              if f (xs i) = a then
                _root_.LIDT.MIPStarRE.LDT.ev strategy.state
                  (_root_.LIDT.MIPStarRE.LDT.opTensor (leftFalse a) (
                    (_root_.LIDT.MIPStarRE.LDT.Pasting.verticalLineMeasurementFamily params strategy u).outcome f))
              else (0 : _root_.LIDT.MIPStarRE.LDT.Error) := by
              rw [Finset.sum_comm]
      _ = ∑ a : _root_.LIDT.MIPStarRE.LDT.Fq params,
            _root_.LIDT.MIPStarRE.LDT.ev strategy.state
              (_root_.LIDT.MIPStarRE.LDT.opTensor (leftFalse a) (Bm.outcome (some a))) := by
              refine Finset.sum_congr rfl ?_
              intro a _
              have hgroup :
                  (∑ f : _root_.LIDT.MIPStarRE.LDT.AxisLinePolynomial params.next,
                    if f (xs i) = a then
                      _root_.LIDT.MIPStarRE.LDT.ev strategy.state
                        (_root_.LIDT.MIPStarRE.LDT.opTensor (leftFalse a) (
                          (_root_.LIDT.MIPStarRE.LDT.Pasting.verticalLineMeasurementFamily params strategy u).outcome f))
                    else (0 : _root_.LIDT.MIPStarRE.LDT.Error))
                    = ∑ f : _root_.LIDT.MIPStarRE.LDT.AxisLinePolynomial params.next,
                        _root_.LIDT.MIPStarRE.LDT.ev strategy.state
                          (_root_.LIDT.MIPStarRE.LDT.opTensor (leftFalse a)
                            (if f (xs i) = a then
                              (_root_.LIDT.MIPStarRE.LDT.Pasting.verticalLineMeasurementFamily params strategy u).outcome f
                            else 0)) := by
                      refine Finset.sum_congr rfl ?_
                      intro f _
                      by_cases hf : f (xs i) = a
                      · simp [hf]
                      · simp [hf, _root_.LIDT.MIPStarRE.LDT.opTensor, _root_.LIDT.MIPStarRE.LDT.ev]
              rw [hgroup, ← _root_.LIDT.MIPStarRE.LDT.ev_finset_sum, ← _root_.LIDT.MIPStarRE.LDT.opTensor_sum_right_finset]
              rw [_root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointRightMeasurement_outcome_some_eq_sum]
  have hdefect_expand :
      _root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect strategy.state A Bm.toSubMeas =
        _root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect strategy.state
          ((_root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointLeftFamily params strategy family k i.1) q)
          ((_root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointRightFamily params strategy family k i.1) q) := by
    rfl
  calc
    (∑ f : _root_.LIDT.MIPStarRE.LDT.AxisLinePolynomial params.next,
      _root_.LIDT.MIPStarRE.LDT.ev strategy.state
        (_root_.LIDT.MIPStarRE.LDT.opTensor
          (∑ gs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params k,
            if ∃ hiSome : (gs i).isSome = true, ((gs i).get hiSome) u ≠ f (xs i) then
              (_root_.LIDT.MIPStarRE.LDT.Pasting.interpolationEligibleSandwichFamily params family k xs).outcome gs
            else 0)
          ((_root_.LIDT.MIPStarRE.LDT.Pasting.verticalLineMeasurementFamily params strategy u).outcome f)))
      ≤ ∑ f : _root_.LIDT.MIPStarRE.LDT.AxisLinePolynomial params.next,
          _root_.LIDT.MIPStarRE.LDT.ev strategy.state
            (_root_.LIDT.MIPStarRE.LDT.opTensor (leftFalse (f (xs i)))
              ((_root_.LIDT.MIPStarRE.LDT.Pasting.verticalLineMeasurementFamily params strategy u).outcome f)) := by
            exact Finset.sum_le_sum fun f _ => hstep f
    _ = ∑ a : _root_.LIDT.MIPStarRE.LDT.Fq params,
          _root_.LIDT.MIPStarRE.LDT.ev strategy.state
            (_root_.LIDT.MIPStarRE.LDT.opTensor (leftFalse a) (Bm.outcome (some a))) := hgrouped
    _ = ∑ a : _root_.LIDT.MIPStarRE.LDT.Fq params,
          _root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect strategy.state
            (_root_.LIDT.MIPStarRE.LDT.postprocess A (fun o => decide (o = some a)))
            (_root_.LIDT.MIPStarRE.LDT.Pasting.singleOutcomeRightSubMeas Bm.toSubMeas (some a)) := by
            refine Finset.sum_congr rfl ?_
            intro a _
            symm
            exact _root_.LIDT.MIPStarRE.LDT.Pasting.qBipartiteConsDefect_postprocess_eq_singleOutcome strategy.state A
                Bm.toSubMeas (some a)
    _ ≤ _root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect strategy.state A Bm.toSubMeas := by
            rw [_root_.LIDT.MIPStarRE.LDT.Pasting.qBipartiteConsDefect_eq_sum_singleOutcome (B := Bm), Fintype.sum_option]
            have hnone_nonneg :
                0 ≤ _root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect strategy.state
                  (_root_.LIDT.MIPStarRE.LDT.postprocess A (fun o => decide (o = none)))
                  (_root_.LIDT.MIPStarRE.LDT.Pasting.singleOutcomeRightSubMeas Bm.toSubMeas none) :=
              _root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect_nonneg strategy.state _ _
            linarith
    _ = _root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect strategy.state
          ((_root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointLeftFamily params strategy family k i.1) q)
          ((_root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointRightFamily params strategy family k i.1) q) := hdefect_expand
