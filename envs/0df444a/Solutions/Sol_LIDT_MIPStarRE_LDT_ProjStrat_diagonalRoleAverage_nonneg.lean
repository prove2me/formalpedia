-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.ProjStrat.diagonalRoleAverage_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T17:57:38.478952+00:00
-- url     : https://prove2.me/submissions/f3ce02aa-c87f-4685-bead-b4cf37b8b673

-- Generated proof for MIPStarRE.LDT.ProjStrat.diagonalRoleAverage_nonneg.
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
    0 ≤ strategy.diagonalRoleAverage := by
  unfold _root_.LIDT.MIPStarRE.LDT.ProjStrat.diagonalRoleAverage
  apply div_nonneg
  · unfold _root_.LIDT.MIPStarRE.LDT.ProjStrat.diagonalLineLeftPointRightFailureProbability
    unfold _root_.LIDT.MIPStarRE.LDT.ProjStrat.diagonalPointLeftLineRightFailureProbability
    have hline :
        0 ≤ (1 / (params.m : _root_.LIDT.MIPStarRE.LDT.Error)) *
          ∑ j : Fin params.m,
            _root_.LIDT.MIPStarRE.LDT.bipartiteConsError strategy.state
              (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.RestrictedDiagonalSample params j))
              (_root_.LIDT.MIPStarRE.LDT.ProjStrat.diagonalLineAnswerFamilyA strategy j)
              (_root_.LIDT.MIPStarRE.LDT.ProjStrat.diagonalPointAnswerFamilyB strategy j) := by
      refine mul_nonneg ?_ ?_
      · positivity
      · refine Finset.sum_nonneg ?_
        intro j _
        exact _root_.LIDT.MIPStarRE.LDT.bipartiteConsError_nonneg strategy.state
          (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.RestrictedDiagonalSample params j))
          (_root_.LIDT.MIPStarRE.LDT.ProjStrat.diagonalLineAnswerFamilyA strategy j)
          (_root_.LIDT.MIPStarRE.LDT.ProjStrat.diagonalPointAnswerFamilyB strategy j)
    have hpoint :
        0 ≤ (1 / (params.m : _root_.LIDT.MIPStarRE.LDT.Error)) *
          ∑ j : Fin params.m,
            _root_.LIDT.MIPStarRE.LDT.bipartiteConsError strategy.state
              (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.RestrictedDiagonalSample params j))
              (_root_.LIDT.MIPStarRE.LDT.ProjStrat.diagonalPointAnswerFamilyA strategy j)
              (_root_.LIDT.MIPStarRE.LDT.ProjStrat.diagonalLineAnswerFamilyB strategy j) := by
      refine mul_nonneg ?_ ?_
      · positivity
      · refine Finset.sum_nonneg ?_
        intro j _
        exact _root_.LIDT.MIPStarRE.LDT.bipartiteConsError_nonneg strategy.state
          (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.RestrictedDiagonalSample params j))
          (_root_.LIDT.MIPStarRE.LDT.ProjStrat.diagonalPointAnswerFamilyA strategy j)
          (_root_.LIDT.MIPStarRE.LDT.ProjStrat.diagonalLineAnswerFamilyB strategy j)
    linarith
  · norm_num
