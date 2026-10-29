-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlice_phaseFivePaper_reindex_to_raw_defect
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T13:57:21.868665+00:00
-- url     : https://prove2.me/submissions/0d3f4485-6be4-4312-82a7-24df2427be85

-- Generated proof for MIPStarRE.LDT.Commutativity.evaluatedSlice_phaseFivePaper_reindex_to_raw_defect.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionUniformSums
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_GCommStability_Scalar_RawSecond
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Products
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_PaperChainPhaseFive
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Completion
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Local
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_CauchySchwarz
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
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
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Theorems.Thm_LIDT_MIPStarRE_LDT_Commutativity_ev_leftTensor_mul_middle_finset_sum

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.Commutativity
end LIDT.MIPStarRE.LDT.Commutativity
namespace LIDT.MIPStarRE.LDT.Commutativity.GCommStability.Scalar
end LIDT.MIPStarRE.LDT.Commutativity.GCommStability.Scalar
namespace LIDT.MIPStarRE.LDT.CommutativityPoints
end LIDT.MIPStarRE.LDT.CommutativityPoints
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries

namespace LIDT

/- Source helpers from MIPStarRE/LDT/Commutativity/ScalarApproximation/PaperChainBasic/Reindexing.lean. -/
/-!
# Reindexing and evaluation utilities for the evaluated-slice paper chain

This file contains finite-reindexing and evaluated-family identities used by
the paper-faithful scalar approximation chain.
-/

@[expose] public section

namespace MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]






/-- Evaluating the slice family at an appended point is postprocessing the slice
measurement by the fiber `{g | g u = a}`. -/
lemma evaluatedPointFamily_appendPoint_outcome
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (x : Fq params) (u : Point params) (a : Fq params) :
    (evaluatedPointFamily params family (appendPoint params u x)).outcome a =
      ∑ g ∈ Finset.univ.filter (fun g : Polynomial params => g u = a),
        (G x).outcome g := by
  simp [evaluatedPointFamily, IdxPolyFamily.evaluatedAtNextPoint, evaluateAt,
    postprocess, hG, truncatePoint_appendPoint, pointHeight_appendPoint]

end MIPStarRE.LDT.Commutativity

end

/- Source helpers from MIPStarRE/LDT/Commutativity/ScalarApproximation/PaperChainPhaseFive.lean. -/
/-!
# Phase-five endpoint for the evaluated-slice paper chain

This file isolates the paper line-87 removal endpoint and the finite
reindexing to the raw scalar `G`-commutativity stability defect.
-/

@[expose] public section

namespace MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Paper-faithful phase-five removal after the right-register swap -/



















/-- Collapse the first-coordinate postprocessing fiber in the raw paper defect.

For fixed `(u,x)` and right prefix `P₂`, summing over evaluated outcomes `a`
expands `G^{u,x}_a = ∑_{g : g(u)=a} G^x_g` and collapses to a polynomial sum. -/
private lemma phaseFivePaper_fiber_sum_ev
    (params : Parameters) [FieldModel params.q]
    (ψ : QuantumState (ι × ι))
    (u : Point params)
    (B T P₂ : MIPStarRE.Quantum.Op ι)
    (Gx : SubMeas (Polynomial params) ι)
    (P₁ : Fq params → MIPStarRE.Quantum.Op ι) :
    (∑ a : Fq params,
      ev ψ
        (leftTensor (ι₂ := ι)
            (((∑ g ∈ Finset.univ.filter
                    (fun g : Polynomial params => g u = a), Gx.outcome g) * B) * T) *
          rightTensor (ι₁ := ι) (P₂ * P₁ a))) =
      ∑ g : Polynomial params,
        ev ψ
          (leftTensor (ι₂ := ι) ((Gx.outcome g * B) * T) *
            rightTensor (ι₁ := ι) (P₂ * P₁ (g u))) := by
  classical
  calc
    ∑ a : Fq params,
        ev ψ
          (leftTensor (ι₂ := ι)
              (((∑ g ∈ Finset.univ.filter
                      (fun g : Polynomial params => g u = a), Gx.outcome g) * B) * T) *
            rightTensor (ι₁ := ι) (P₂ * P₁ a))
      = ∑ a : Fq params,
          ∑ g ∈ Finset.univ.filter (fun g : Polynomial params => g u = a),
            ev ψ
              (leftTensor (ι₂ := ι) (((1 : MIPStarRE.Quantum.Op ι) * Gx.outcome g * B) * T) *
                rightTensor (ι₁ := ι) (P₂ * P₁ a)) := by
          refine Finset.sum_congr rfl ?_
          intro a _
          simpa [one_mul] using
            (ev_leftTensor_mul_middle_finset_sum (ι := ι)
              (s := Finset.univ.filter (fun g : Polynomial params => g u = a))
              (ψ := ψ) (A := (1 : MIPStarRE.Quantum.Op ι)) (C := B) (R := T)
              (D := P₂ * P₁ a) (B := fun g : Polynomial params => Gx.outcome g))
    _ = ∑ a : Fq params,
          ∑ g ∈ Finset.univ.filter (fun g : Polynomial params => g u = a),
            ev ψ
              (leftTensor (ι₂ := ι) (((1 : MIPStarRE.Quantum.Op ι) * Gx.outcome g * B) * T) *
                rightTensor (ι₁ := ι) (P₂ * P₁ (g u))) := by
          refine Finset.sum_congr rfl ?_
          intro a _
          refine Finset.sum_congr rfl ?_
          intro g hg
          have hgu : g u = a := (Finset.mem_filter.mp hg).2
          simp [hgu]
    _ = ∑ g : Polynomial params,
          ev ψ
            (leftTensor (ι₂ := ι) (((1 : MIPStarRE.Quantum.Op ι) * Gx.outcome g * B) * T) *
              rightTensor (ι₁ := ι) (P₂ * P₁ (g u))) := by
          simpa using
            (Finset.sum_fiberwise Finset.univ (fun g : Polynomial params => g u)
              (fun g : Polynomial params =>
                ev ψ
                  (leftTensor (ι₂ := ι)
                    (((1 : MIPStarRE.Quantum.Op ι) * Gx.outcome g * B) * T) *
                    rightTensor (ι₁ := ι) (P₂ * P₁ (g u)))) )
    _ = ∑ g : Polynomial params,
          ev ψ
            (leftTensor (ι₂ := ι) ((Gx.outcome g * B) * T) *
              rightTensor (ι₁ := ι) (P₂ * P₁ (g u))) := by
          simp

/-- Pointwise expansion of the swapped paper defect after writing the first point as `(u,x)`.

The statement keeps point measurements in the local `evaluatedSlicePointMeas`
notation; the final reindexing lemma rewrites those to `strategy.pointMeasurement`
when matching `gCommStabilityTwoRawScalarDefect`. -/
private lemma evaluatedSlicePhaseFivePaperSwappedDefect_appendPoint_expansion
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (x : Fq params) (u : Point params) (vy : Point params.next) :
    evaluatedSlicePhaseFivePaperSwappedDefect params strategy family G
        (appendPoint params u x, vy) =
      ∑ g : Polynomial params, ∑ b : Fq params,
        ev strategy.state
          (leftTensor (ι₂ := ι)
              ((G x).outcome g *
                (evaluatedPointFamily params family vy).outcome b *
                (1 - (G x).total)) *
            rightTensor (ι₁ := ι)
              (((evaluatedSlicePointMeas params strategy vy).outcome b) *
                ((evaluatedSlicePointMeas params strategy
                    (appendPoint params u x)).outcome (g u)))) := by
  classical
  calc
    evaluatedSlicePhaseFivePaperSwappedDefect params strategy family G (appendPoint params u x, vy)
        = ∑ b : Fq params, ∑ g : Polynomial params,
            ev strategy.state
              (leftTensor (ι₂ := ι)
                  ((G x).outcome g *
                    (evaluatedPointFamily params family vy).outcome b *
                    (1 - (G x).total)) *
                rightTensor (ι₁ := ι)
                  (((evaluatedSlicePointMeas params strategy vy).outcome b) *
                    ((evaluatedSlicePointMeas params strategy (appendPoint params u x)).outcome
                      (g u)))) := by
          dsimp [evaluatedSlicePhaseFivePaperSwappedDefect, evaluatedSliceFirstFactor,
            evaluatedSliceSecondFactor]
          rw [pointHeight_appendPoint]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl ?_
          intro b _
          have hfiber :=
            phaseFivePaper_fiber_sum_ev (ι := ι) params strategy.state u
              ((evaluatedPointFamily params family vy).outcome b)
              (1 - (G x).total)
              ((evaluatedSlicePointMeas params strategy vy).outcome b)
              (G x)
              (fun a : Fq params =>
                (evaluatedSlicePointMeas params strategy (appendPoint params u x)).outcome a)
          simpa [evaluatedPointFamily_appendPoint_outcome, hG, mul_assoc] using hfiber
    _ = ∑ g : Polynomial params, ∑ b : Fq params,
            ev strategy.state
              (leftTensor (ι₂ := ι)
                  ((G x).outcome g *
                    (evaluatedPointFamily params family vy).outcome b *
                    (1 - (G x).total)) *
                rightTensor (ι₁ := ι)
                  (((evaluatedSlicePointMeas params strategy vy).outcome b) *
                    ((evaluatedSlicePointMeas params strategy (appendPoint params u x)).outcome
                      (g u)))) := by
          rw [Finset.sum_comm]



end MIPStarRE.LDT.Commutativity

end

end LIDT

open LIDT
/-!
# Phase-five endpoint for the evaluated-slice paper chain

This file isolates the paper line-87 removal endpoint and the finite
reindexing to the raw scalar `G`-commutativity stability defect.
-/

@[expose] public section

open LIDT.MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Paper-faithful phase-five removal after the right-register swap -/

theorem solution
    (params : _root_.LIDT.MIPStarRE.LDT.Parameters) [_root_.LIDT.MIPStarRE.LDT.FieldModel params.q]
    (strategy : _root_.LIDT.MIPStarRE.LDT.SymStrat params.next ι)
    (family : _root_.LIDT.MIPStarRE.LDT.IdxPolyFamily params ι)
    (G : _root_.LIDT.MIPStarRE.LDT.Fq params → _root_.LIDT.MIPStarRE.LDT.SubMeas (_root_.LIDT.MIPStarRE.LDT.Polynomial params) ι)
    (hG : ∀ x, G x = (family.meas x).toSubMeas) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params))
        (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePhaseFivePaperSwappedDefect params strategy family G) =
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params))
        (_root_.LIDT.MIPStarRE.LDT.Commutativity.gCommStabilityTwoRawScalarDefect params strategy family G) := by
  classical
  calc
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params))
        (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePhaseFivePaperSwappedDefect params strategy family G)
        = _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params.next)) (fun ux =>
            _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params.next)) (fun vy =>
              _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePhaseFivePaperSwappedDefect params strategy family G (ux, vy))) := by
          simpa using
            (_root_.LIDT.MIPStarRE.LDT.avgOver_uniform_prod (α := _root_.LIDT.MIPStarRE.LDT.Point params.next) (β := _root_.LIDT.MIPStarRE.LDT.Point params.next)
              (f := fun ux vy =>
                _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePhaseFivePaperSwappedDefect params strategy family G (ux, vy)))
    _ = _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params)) (fun x =>
          _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params)) (fun u =>
            _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params.next)) (fun vy =>
              _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePhaseFivePaperSwappedDefect params strategy family G
                (_root_.LIDT.MIPStarRE.LDT.appendPoint params u x, vy)))) := by
          rw [_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.avgOver_uniform_pointNext_decompose params]
    _ = _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params)) (fun x =>
          _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params)) (fun u =>
            _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params.next)) (fun vy =>
              ∑ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params, ∑ b : _root_.LIDT.MIPStarRE.LDT.Fq params,
                _root_.LIDT.MIPStarRE.LDT.ev strategy.state
                  (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                      ((G x).outcome g *
                        (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedPointFamily params family vy).outcome b *
                        (1 - (G x).total)) *
                    _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι)
                      (((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas params strategy vy).outcome b) *
                        ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas params strategy (_root_.LIDT.MIPStarRE.LDT.appendPoint params u x)).outcome
                          (g u))))))) := by
          apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
          intro x
          apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
          intro u
          apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
          intro vy
          exact evaluatedSlicePhaseFivePaperSwappedDefect_appendPoint_expansion
            params strategy family G hG x u vy
    _ = _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params)) (fun x =>
          _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params.next)) (fun vy =>
            _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params)) (fun u =>
              ∑ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params, ∑ b : _root_.LIDT.MIPStarRE.LDT.Fq params,
                _root_.LIDT.MIPStarRE.LDT.ev strategy.state
                  (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                      ((G x).outcome g *
                        (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedPointFamily params family vy).outcome b *
                        (1 - (G x).total)) *
                    _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι)
                      (((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas params strategy vy).outcome b) *
                        ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas params strategy (_root_.LIDT.MIPStarRE.LDT.appendPoint params u x)).outcome
                          (g u))))))) := by
          apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
          intro x
          exact _root_.LIDT.MIPStarRE.LDT.avgOver_uniform_comm (α := _root_.LIDT.MIPStarRE.LDT.Point params) (β := _root_.LIDT.MIPStarRE.LDT.Point params.next)
            (fun u vy =>
              ∑ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params, ∑ b : _root_.LIDT.MIPStarRE.LDT.Fq params,
                _root_.LIDT.MIPStarRE.LDT.ev strategy.state
                  (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                      ((G x).outcome g *
                        (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedPointFamily params family vy).outcome b *
                        (1 - (G x).total)) *
                    _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι)
                      (((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas params strategy vy).outcome b) *
                        ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas params strategy (_root_.LIDT.MIPStarRE.LDT.appendPoint params u x)).outcome
                          (g u)))))
    _ = _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params))
          (_root_.LIDT.MIPStarRE.LDT.Commutativity.gCommStabilityTwoRawScalarDefect params strategy family G) := by
          apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
          intro x
          unfold _root_.LIDT.MIPStarRE.LDT.Commutativity.gCommStabilityTwoRawScalarDefect
          apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
          intro vy
          apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
          intro u
          simp [_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas, _root_.LIDT.MIPStarRE.LDT.Parameters.next]
