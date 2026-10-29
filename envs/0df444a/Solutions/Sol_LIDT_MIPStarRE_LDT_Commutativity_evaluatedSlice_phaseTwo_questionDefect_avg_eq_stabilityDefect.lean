-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlice_phaseTwo_questionDefect_avg_eq_stabilityDefect
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T14:00:33.018506+00:00
-- url     : https://prove2.me/submissions/6ebc25a1-cdde-4613-a138-1e3360e1a595

-- Generated proof for MIPStarRE.LDT.Commutativity.evaluatedSlice_phaseTwo_questionDefect_avg_eq_stabilityDefect.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_GCommStability_Scalar_First
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Products
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_ProcessedG_PhaseTwo
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
import Theorems.Thm_LIDT_MIPStarRE_LDT_Commutativity_avgOver_avgOver_phaseTwo_linear
import Theorems.Thm_LIDT_MIPStarRE_LDT_Commutativity_evaluatedSlicePhaseTwoQuestionDefect_append_eq_sum_poly
import Theorems.Thm_LIDT_MIPStarRE_LDT_Commutativity_postprocess_sandwichByOuter_prod_snd_outcome

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

end LIDT

open LIDT
/-!
# Phase 2 stability defect infrastructure

Internal helper definitions and lemmas for the Phase 2 scalar bridge in
`ProcessedG`.  These definitions extract and bound the one-dimensional stability
defect controlled by `gCommStability_scalar` (the paper's `clm:g-comm-stability`),
reindex the question-level defect into the stability defect via finite
marginalization, and perform the subtraction algebra that rewrites the phase-2
insertion/removal difference as the negative defect.
-/

@[expose] public section

open LIDT.MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem solution
    (params : _root_.LIDT.MIPStarRE.LDT.Parameters) [_root_.LIDT.MIPStarRE.LDT.FieldModel params.q]
    (strategy : _root_.LIDT.MIPStarRE.LDT.SymStrat params.next ι)
    (family : _root_.LIDT.MIPStarRE.LDT.IdxPolyFamily params ι)
    (G : _root_.LIDT.MIPStarRE.LDT.Fq params → _root_.LIDT.MIPStarRE.LDT.SubMeas (_root_.LIDT.MIPStarRE.LDT.Polynomial params) ι) :
  _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params))
      (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePhaseTwoQuestionDefect params strategy family G) =
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params))
      (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePhaseTwoStabilityDefect params strategy family G) := by
  classical
  let defect := _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePhaseTwoQuestionDefect params strategy family G
  have hprod :
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params)) defect =
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params.next))
        (fun q2 => _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params.next))
          (fun q1 => defect (q1, q2))) := by
    calc
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params)) defect =
          _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params.next × _root_.LIDT.MIPStarRE.LDT.Point params.next))
            (fun qq => defect qq) := by
            rfl
      _ = _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params.next × _root_.LIDT.MIPStarRE.LDT.Point params.next))
            (fun qq => defect (qq.2, qq.1)) := by
            simpa [Prod.swap] using
              (_root_.LIDT.MIPStarRE.LDT.avgOver_uniform_equiv
                (e := Equiv.prodComm (_root_.LIDT.MIPStarRE.LDT.Point params.next) (_root_.LIDT.MIPStarRE.LDT.Point params.next))
                (f := fun qq : _root_.LIDT.MIPStarRE.LDT.Point params.next × _root_.LIDT.MIPStarRE.LDT.Point params.next => defect qq))
      _ = _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params.next))
            (fun q2 => _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params.next))
              (fun q1 => defect (q1, q2))) := by
            simpa using
              (_root_.LIDT.MIPStarRE.LDT.avgOver_uniform_prod (α := _root_.LIDT.MIPStarRE.LDT.Point params.next) (β := _root_.LIDT.MIPStarRE.LDT.Point params.next)
                (f := fun q2 q1 => defect (q1, q2)))
  have hdecomposeSecond :
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params.next))
        (fun q2 => _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params.next))
          (fun q1 => defect (q1, q2))) =
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params))
        (fun y => _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params))
          (fun v => _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params.next))
            (fun q1 => defect (q1, _root_.LIDT.MIPStarRE.LDT.appendPoint params v y)))) := by
    simpa using
      (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.avgOver_uniform_pointNext_decompose (params := params)
        (f := fun q2 => _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params.next))
          (fun q1 => defect (q1, q2))))
  have hbody :
      ∀ y : _root_.LIDT.MIPStarRE.LDT.Fq params,
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params))
          (fun v => _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params.next))
            (fun q1 => defect (q1, _root_.LIDT.MIPStarRE.LDT.appendPoint params v y))) =
        _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePhaseTwoStabilityDefect params strategy family G y := by
    intro y
    let Ffun : _root_.LIDT.MIPStarRE.LDT.Point params.next → _root_.LIDT.MIPStarRE.LDT.Polynomial params → _root_.LIDT.MIPStarRE.LDT.Fq params → _root_.LIDT.MIPStarRE.Quantum.Op ι :=
      fun q1 g a =>
        (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedPointFamily params family q1).outcome a *
          ((family.meas y).toSubMeas.outcome g) *
          (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedPointFamily params family q1).outcome a
    let Pfun : _root_.LIDT.MIPStarRE.LDT.Polynomial params → _root_.LIDT.MIPStarRE.LDT.Point params → _root_.LIDT.MIPStarRE.Quantum.Op ι :=
      fun g v => (strategy.pointMeasurement (_root_.LIDT.MIPStarRE.LDT.appendPoint params v y)).outcome (g v)
    let R : _root_.LIDT.MIPStarRE.Quantum.Op ι := 1 - (G y).total
    have hFavg :
        ∀ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params,
          _root_.LIDT.MIPStarRE.LDT.averageOperatorOverDistribution (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params.next))
            (fun q1 => ∑ a : _root_.LIDT.MIPStarRE.LDT.Fq params, Ffun q1 g a) =
          (_root_.LIDT.MIPStarRE.LDT.Commutativity.gCommStabilityR params family y).outcome g := by
      intro g
      unfold _root_.LIDT.MIPStarRE.LDT.Commutativity.gCommStabilityR _root_.LIDT.MIPStarRE.LDT.averageIdxSubMeas
      refine _root_.LIDT.MIPStarRE.LDT.averageOperatorOverDistribution_congr _ _ _ (fun q1 => ?_)
      rw [_root_.LIDT.MIPStarRE.LDT.Commutativity.postprocess_sandwichByOuter_prod_snd_outcome]
    have hPavg :
        ∀ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params,
          _root_.LIDT.MIPStarRE.LDT.averageOperatorOverDistribution (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params))
            (fun v => Pfun g v) =
          _root_.LIDT.MIPStarRE.LDT.IdxPolyFamily.averagedSlicePointEvaluationOperator strategy y g := by
      intro g
      rfl
    calc
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params))
          (fun v => _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params.next))
            (fun q1 => defect (q1, _root_.LIDT.MIPStarRE.LDT.appendPoint params v y))) =
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params))
          (fun v => _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params.next))
            (fun q1 => ∑ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params, ∑ a : _root_.LIDT.MIPStarRE.LDT.Fq params,
              _root_.LIDT.MIPStarRE.LDT.ev strategy.state
                (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (Ffun q1 g a * R) *
                  _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (Pfun g v)))) := by
          apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
          intro v
          apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
          intro q1
          simpa [defect, Ffun, Pfun, R] using
            _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePhaseTwoQuestionDefect_append_eq_sum_poly
              params strategy family G q1 v y
      _ = ∑ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params,
            _root_.LIDT.MIPStarRE.LDT.ev strategy.state
              (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                  ((_root_.LIDT.MIPStarRE.LDT.averageOperatorOverDistribution (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params.next))
                    (fun q1 => ∑ a : _root_.LIDT.MIPStarRE.LDT.Fq params, Ffun q1 g a)) * R) *
                _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι)
                  (_root_.LIDT.MIPStarRE.LDT.averageOperatorOverDistribution (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params))
                    (fun v => Pfun g v))) := by
          exact _root_.LIDT.MIPStarRE.LDT.Commutativity.avgOver_avgOver_phaseTwo_linear
            (𝒟Q := _root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params.next))
            (𝒟V := _root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params))
            (ψ := strategy.state) (F := Ffun) (P := Pfun) (R := R)
      _ = _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePhaseTwoStabilityDefect params strategy family G y := by
          unfold _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePhaseTwoStabilityDefect
          refine Finset.sum_congr rfl ?_
          intro g _
          rw [hFavg g, hPavg g]
  rw [hprod, hdecomposeSecond]
  apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
  intro y
  exact hbody y
