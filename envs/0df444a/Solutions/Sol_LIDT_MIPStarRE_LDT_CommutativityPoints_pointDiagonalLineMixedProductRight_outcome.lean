-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.CommutativityPoints.pointDiagonalLineMixedProductRight_outcome
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T14:15:26.468738+00:00
-- url     : https://prove2.me/submissions/3ec72e3b-6af1-4efe-8611-afbabcc4f9c8

-- Generated proof for MIPStarRE.LDT.CommutativityPoints.pointDiagonalLineMixedProductRight_outcome.
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
    (q : _root_.LIDT.MIPStarRE.LDT.CommutativityPoints.PointPairDiagonalLineQuestion params)
    (a b : _root_.LIDT.MIPStarRE.LDT.Fq params) :
    ((_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.toIdxOpFamily
        (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.pointDiagonalLineMixedProductRight params strategy) q).outcome (a, b)) =
      _root_.LIDT.MIPStarRE.LDT.opTensor
        ((strategy.pointMeasurement (q.1.pointAt q.2.2)).outcome b)
        ((_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.sampledDiagonalLineEvaluation params strategy (q.1, q.2.1)).outcome a) := by
  classical
  suffices h :
      ∑ ab : _root_.LIDT.MIPStarRE.LDT.Fq params × _root_.LIDT.MIPStarRE.LDT.Fq params with ab.2 = a ∧ ab.1 = b,
        _root_.LIDT.MIPStarRE.LDT.opTensor ((strategy.pointMeasurement (q.1.pointAt q.2.2)).outcome ab.1)
          ((_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.sampledDiagonalLineEvaluation params strategy (q.1, q.2.1)).outcome ab.2) =
      _root_.LIDT.MIPStarRE.LDT.opTensor ((strategy.pointMeasurement (q.1.pointAt q.2.2)).outcome b)
        ((_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.sampledDiagonalLineEvaluation params strategy (q.1, q.2.1)).outcome a) by
    simpa [_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.pointDiagonalLineMixedProductRight, _root_.LIDT.MIPStarRE.LDT.CommutativityPoints.tensorProductSubMeas,
      _root_.LIDT.MIPStarRE.LDT.postprocess, Prod.swap, _root_.LIDT.MIPStarRE.LDT.IdxSubMeas.toIdxOpFamily, _root_.LIDT.MIPStarRE.LDT.SubMeas.toOpFamily,
      _root_.LIDT.MIPStarRE.LDT.leftTensor_mul_rightTensor_eq_opTensor] using h
  have hfilter :
      (Finset.univ.filter (fun ab : _root_.LIDT.MIPStarRE.LDT.Fq params × _root_.LIDT.MIPStarRE.LDT.Fq params => ab.2 = a ∧ ab.1 = b)) =
        {(b, a)} := by
    ext ab
    rcases ab with ⟨a', b'⟩
    simp [and_comm]
  rw [hfilter]
  simp
