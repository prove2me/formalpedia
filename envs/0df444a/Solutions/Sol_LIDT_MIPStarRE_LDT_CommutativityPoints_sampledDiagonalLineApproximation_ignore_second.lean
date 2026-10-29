-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.CommutativityPoints.sampledDiagonalLineApproximation_ignore_second
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T14:25:03.064218+00:00
-- url     : https://prove2.me/submissions/4fa8018d-21a0-49b9-9e1d-fcc0e261623e

-- Generated proof for MIPStarRE.LDT.CommutativityPoints.sampledDiagonalLineApproximation_ignore_second.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_QuantumNonneg
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyFailures
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
import Theorems.Thm_LIDT_MIPStarRE_LDT_CommutativityPoints_avgOver_pointPairSharedDiagonalLine_ignore_second
import Theorems.Thm_LIDT_MIPStarRE_LDT_CommutativityPoints_sampledDiagonalLineApproximation_pointWithDiagonalLine

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.CommutativityPoints
end LIDT.MIPStarRE.LDT.CommutativityPoints

namespace LIDT

end LIDT

open LIDT
/-!
# Section 10 commutativity points: shared-line helpers

Compatibility lemmas between sampled point pairs and shared-diagonal line
questions, used by both the lift and drop comparisons.

## References

- `references/ldt-paper/commutativity-points.tex`
- `blueprint/src/chapter/ch08_commutativity.tex`
-/

@[expose] public section

open LIDT.MIPStarRE.LDT.CommutativityPoints

open MIPStarRE.LDT.GlobalVariance (PointPairQuestion)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open scoped _root_.Matrix MatrixOrder ComplexOrder BigOperators

theorem solution
    (params : _root_.LIDT.MIPStarRE.LDT.Parameters)
    [_root_.LIDT.MIPStarRE.LDT.FieldModel params.q]
    (strategy : _root_.LIDT.MIPStarRE.LDT.SymStrat params ι)
    (eps delta gamma : _root_.LIDT.MIPStarRE.LDT.Error)
    (hgood : strategy.IsGood eps delta gamma) :
    _root_.LIDT.MIPStarRE.LDT.SDDOpRel strategy.state
      (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.pointPairSharedDiagonalLineDistribution params)
      (fun q =>
        _root_.LIDT.MIPStarRE.LDT.OpFamily.leftPlacedOpFamily (ιB := ι)
          ((strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas))
      (fun q =>
        _root_.LIDT.MIPStarRE.LDT.OpFamily.rightPlacedOpFamily (ιA := ι)
          (_root_.LIDT.MIPStarRE.LDT.SubMeas.toOpFamily (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.sampledDiagonalLineEvaluation params strategy (q.1, q.2.1))))
      (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.pointDiagonalLineApproxError params gamma) := by
  rcases _root_.LIDT.MIPStarRE.LDT.CommutativityPoints.sampledDiagonalLineApproximation_pointWithDiagonalLine
    params strategy eps delta gamma hgood with ⟨happrox⟩
  constructor
  calc
    _root_.LIDT.MIPStarRE.LDT.sddErrorOp strategy.state
        (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.pointPairSharedDiagonalLineDistribution params)
        (fun q =>
          _root_.LIDT.MIPStarRE.LDT.OpFamily.leftPlacedOpFamily (ιB := ι)
            ((strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas))
        (fun q =>
          _root_.LIDT.MIPStarRE.LDT.OpFamily.rightPlacedOpFamily (ιA := ι)
            (_root_.LIDT.MIPStarRE.LDT.SubMeas.toOpFamily (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.sampledDiagonalLineEvaluation params strategy (q.1, q.2.1))))
      = _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.pointPairSharedDiagonalLineDistribution params)
          (fun q =>
            _root_.LIDT.MIPStarRE.LDT.qSDD strategy.state
              ((_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftLeft (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.sampledPointMeasurement params strategy)) (q.1, q.2.1))
              ((_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftRight (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.sampledDiagonalLineEvaluation params strategy))
                (q.1, q.2.1))) := by
            unfold _root_.LIDT.MIPStarRE.LDT.sddErrorOp
            apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
            intro q
            unfold _root_.LIDT.MIPStarRE.LDT.qSDDOp _root_.LIDT.MIPStarRE.LDT.qSDD _root_.LIDT.MIPStarRE.LDT.qSDDCore _root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftLeft _root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftRight
              _root_.LIDT.MIPStarRE.LDT.OpFamily.leftPlacedOpFamily _root_.LIDT.MIPStarRE.LDT.OpFamily.rightPlacedOpFamily
              _root_.LIDT.MIPStarRE.LDT.CommutativityPoints.sampledPointMeasurement _root_.LIDT.MIPStarRE.LDT.CommutativityPoints.sampledPointFromDiagonalQuestion _root_.LIDT.MIPStarRE.LDT.SubMeas.toOpFamily
            rfl
    _ = _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.pointWithDiagonalLineDistribution params)
          (fun q =>
            _root_.LIDT.MIPStarRE.LDT.qSDD strategy.state
              ((_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftLeft (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.sampledPointMeasurement params strategy)) q)
              ((_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftRight (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.sampledDiagonalLineEvaluation params strategy)) q)) := by
            exact _root_.LIDT.MIPStarRE.LDT.CommutativityPoints.avgOver_pointPairSharedDiagonalLine_ignore_second params
              (fun q =>
                _root_.LIDT.MIPStarRE.LDT.qSDD strategy.state
                  ((_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftLeft (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.sampledPointMeasurement params strategy)) q)
                  ((_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftRight (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.sampledDiagonalLineEvaluation params strategy)) q))
    _ = _root_.LIDT.MIPStarRE.LDT.sddError strategy.state
          (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.pointWithDiagonalLineDistribution params)
          (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftLeft (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.sampledPointMeasurement params strategy))
          (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftRight (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.sampledDiagonalLineEvaluation params strategy)) := by
            rfl
    _ ≤ _root_.LIDT.MIPStarRE.LDT.CommutativityPoints.pointDiagonalLineApproxError params gamma := happrox
