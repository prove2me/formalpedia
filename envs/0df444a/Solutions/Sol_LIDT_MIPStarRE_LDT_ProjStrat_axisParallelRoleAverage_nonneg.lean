-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.ProjStrat.axisParallelRoleAverage_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T17:57:38.442644+00:00
-- url     : https://prove2.me/submissions/9582631d-6dbc-40f2-819f-b433b81203d6

-- Generated proof for MIPStarRE.LDT.ProjStrat.axisParallelRoleAverage_nonneg.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionUniformSums
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyBiProj_DirectSum
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyBiProj_Measurements
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyFailures
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyRole_Algebra
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyRole_Core
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.ProjStrat
end LIDT.MIPStarRE.LDT.ProjStrat

namespace LIDT

end LIDT

open LIDT
/-!
# Role-Register Averaging: Goodness Bound

This module packages the branch equalities into the three-times-error goodness
bound for the role-register symmetric strategy.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

open LIDT.MIPStarRE.LDT

open MIPStarRE.Quantum

open LIDT.MIPStarRE.LDT.ProjStrat

theorem solution
    {params : _root_.LIDT.MIPStarRE.LDT.Parameters} [_root_.LIDT.MIPStarRE.LDT.FieldModel params.q]
    {ιA : Type*} [Fintype ιA] [DecidableEq ιA]
    {ιB : Type*} [Fintype ιB] [DecidableEq ιB]
    (strategy : _root_.LIDT.MIPStarRE.LDT.ProjStrat params ιA ιB) :
    0 ≤ strategy.axisParallelRoleAverage := by
  unfold _root_.LIDT.MIPStarRE.LDT.ProjStrat.axisParallelRoleAverage
  apply div_nonneg
  · have hline : 0 ≤ strategy.axisParallelLineLeftPointRightFailureProbability := by
      unfold _root_.LIDT.MIPStarRE.LDT.ProjStrat.axisParallelLineLeftPointRightFailureProbability
      exact _root_.LIDT.MIPStarRE.LDT.bipartiteConsError_nonneg strategy.state
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.AxisParallelTestSample params))
        (_root_.LIDT.MIPStarRE.LDT.ProjStrat.axisParallelLineAnswerFamilyA strategy)
        (_root_.LIDT.MIPStarRE.LDT.ProjStrat.axisParallelPointAnswerFamilyB strategy)
    have hpoint : 0 ≤ strategy.axisParallelPointLeftLineRightFailureProbability := by
      unfold _root_.LIDT.MIPStarRE.LDT.ProjStrat.axisParallelPointLeftLineRightFailureProbability
      exact _root_.LIDT.MIPStarRE.LDT.bipartiteConsError_nonneg strategy.state
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.AxisParallelTestSample params))
        (_root_.LIDT.MIPStarRE.LDT.ProjStrat.axisParallelPointAnswerFamilyA strategy)
        (_root_.LIDT.MIPStarRE.LDT.ProjStrat.axisParallelLineAnswerFamilyB strategy)
    linarith
  · norm_num
